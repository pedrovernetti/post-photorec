#!/usr/bin/env python3

# =============================================================================================
#
# This program is free software: you can redistribute it and/or modify it under the terms of
# the GNU General Public License as published by the Free Software Foundation, either version
# 3 of the License, or (at your option) any later version.
# This program is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY;
# without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
# See the GNU General Public License for more details.
# This script must/should come together with a copy of the GNU General Public License. If not,
# access <http://www.gnu.org/licenses/> to find and read it.
#
# Author: Pedro Vernetti G.
# Name: Post-PhotoRec
# Description: Tool to auto-organize files recovered by PhotoRec and similar tools.
#
# #  In order to have this script working (if it is currently not), run 'install.sh'. In case
#    it is missing or does not work, follow these steps:
# 1. install libmediainfo-dev using your package manager;                 .
# 2. install pip (Python package installer) using your package manager;   .
# 3. with pip, install cchardet, lxml, pymediainfo, pillow, pypdf2,       .
#    olefile and fonttools;                                               .
# 4. Make sure this script has execution permission.                      .
#
# =============================================================================================

import sys, os, stat, re, mmap, codecs, json, gzip, filecmp
from unicodedata import category as ucategory, normalize as unormalize
from zipfile import ZipFile as ZIPFile

import cchardet
from lxml import html, etree, objectify
from pymediainfo import MediaInfo
from PIL import Image
from PyPDF2 import PdfFileReader as PDFFile
from PyPDF2.generic import IndirectObject as PDFIndirectObject
try: from olefile import OleFileIO as OLEFile
except: from OleFileIO_PL import OleFileIO as OLEFile
from fontTools import ttLib



# VERBOSITY FUNCTIONS

def helpMessage():
    command = os.path.split(sys.argv[0])[-1]
    message = """
Usage: """ + command + """ [OPTIONS]... DIRECTORY_PATH [OPTIONS]...

For a given directory containing unsorted and meaninglessly-named files, removes
the empty ones, deduplicates them, renames them more meaningfully, fixes
some file extensions and organizes everything in a better directory structure.

Example: """ + command + """ -r log,xml,pyc -n /path/to/recovered_files_dir

 Options:

  -h        Display this help message and exits
  -D        Do not remove duplicate files
  -d        Ignore file extension when deduplicating files
  -J        Do not remove junk files (well known to be usually unwanted)
  -k        Keep directory structure (do not move files)
  -n        Only rename/remove files with photorec-generated names
  -Q        No real-time progress information
  -q        Quiet mode (no verbosity)
  -r EXTS   Remove files with any of the given (comma-separated) extension(s)
  -x [DEV]  Run PhotoRec on DEV (device or image path) before anything else
  -z        Do not remove empty (0B) files

"""
    sys.__stdout__.write(message)
    exit(0)

def error( message, whatToReturn ):
    sys.stderr.write('\x1B[31;1mError: ' + message + '\n')
    exit(whatToReturn)

def progress( message, done, total ):
    progressLen = (len(str(total)) * 2) + 1
    p = '\x1B[2m' + str(done) + r'/' + str(total) + '\x1B[0m'
    sys.stdout.write('\r' + message + r' ' + p.ljust(progressLen) + ('\b' * (progressLen - len(p))))

def _num( x ):
    return (str(x) if (x > 0) else r'No')

def _unmute():
    sys.stderr = sys.__stderr__
    sys.stdout = sys.__stdout__

def _mute():
    try: sys.stderr = sys.stdout = open(os.devnull, r'w')
    except: _unmute()



# UTILITY FUNCTION

def longestCommonPrefix( stringList ):
    if (not stringList): return r''
    shortest = min(stringList, key=len)
    for i, currentChar in enumerate(shortest):
        for other in stringList:
            if (other[i] != currentChar): return shortest[:i]
    return shortest

def split( l, chunkMaxSize ):
    for i in range(0, len(l), chunkMaxSize):
        yield l[i:(i + chunkMaxSize)]



# TEXT NORMALIZATION FUNCTION

_ucats = {r'Cc', r'Cf', r'Co', r'Cs'}
_table = dict.fromkeys(i for i in range(sys.maxunicode) if (ucategory(chr(i)) in _ucats))
_table = { cat:r' ' for cat in _table}
_table[ord('\n')] = r' '
_table[ord('\r')] = r' '
_table[ord(r'?')] = r' '
_table[ord(r'*')] = r' '
_table[ord('\x22')] = '\x27\x27'
_table[ord(r'/')] = r' - '
_table[ord('\\')] = r' - '
_table[ord(r':')] = r' - '
_table[ord(r'|')] = r' - '
_table[ord(r'<')] = r'('
_table[ord(r'>')] = r')'

def _normalized( stringOrStrings ):
    if (stringOrStrings is None):
    	return r''
    elif (isinstance(stringOrStrings, list)):
        return [_normalized(string) for string in stringOrStrings]
    elif (isinstance(stringOrStrings, dict)):
        return dict((key, _normalized(string)) for key, string in stringOrStrings.items())
    normalized = unormalize(r'NFC', stringOrStrings.translate(_table)).strip()
    return re.sub(r'\s+', r' ', re.sub(r'^- ', r'', re.sub(r'( - )+', r' - ', normalized)))



# XML PARSING FUNCTION

def _parsedXML( file ):
    try: parsedXML = etree.parse(file, etree.XMLParser(remove_blank_text=True, remove_comments=True))
    except: return None
    for element in parsedXML.getroot().getiterator():
        if (not hasattr(element.tag, r'find')): continue
        position = element.tag.find(r'}')
        if (position >= 0): element.tag = element.tag[(position + 1):]
    return parsedXML



# CONTENT ANALYSIS FUNCTIONS

def fileContains( filePath, what ):
    with open(filePath, r'rb', 0) as f, mmap.mmap(f.fileno(), 0, access=mmap.ACCESS_READ) as s:
        if (s.find(what) != -1): return True
    return False

def removeFilesContaining( files, extension, what ):
    buffer = []
    for i in range(0, len(files)):
        if (files[i].endswith(extension)):
            if (fileContains(files[i], what)):
                os.remove(files[i])
                continue
        buffer.append(files[i])
    return buffer

def decodedFileContent( file ):
    try: content = file.read()
    except: return r''
    try:
        encoding = cchardet.detect(content)[r'encoding']
        encoding = codecs.lookup(encoding if (encoding is not None) else r'utf-8').name
    except:
        encoding = r'utf-8'
    content = content.decode(encoding, r'ignore')
    return content.strip()



# METADATA-TO-FILENAME FUNCTIONS

def nonEXIFImageFilename( currentName, imageInfo ):
    date = imageInfo.get(r'Creation Time', r'').replace(r':', r'-')
    isScreenshot = r'screenshot' in imageInfo.get(r'Software', r'').lower()
    title = r''
    author = r''
    return os.path.split(currentName)[-1]

def imageFilename( currentName ):
    _mute()
    try: image = Image.open(currentName, r'r')
    except: return os.path.split(currentName)[-1]
    try: EXIF = image._getexif()
    except: EXIF = None
    if (not EXIF):
        try:
            image.load()
            EXIF = image.info.get(r'exif', None) #TODO: must parse it into a dict()
        except:
            _unmute()
            return os.path.split(currentName)[-1]
        if (not EXIF):
            newFilename = nonEXIFImageFilename(currentName, image.info)
            image.close()
            _unmute()
            return newFilename
        else:
            image.close()
    try:
        cameraModel = EXIF.get(272, EXIF.get(50709, EXIF.get(50708, EXIF.get(271, EXIF.get(50735)))))
        if (isinstance(cameraModel, bytes)): cameraModel = cameraModel.decode(r'utf-8', r'ignore')
        cameraModel = re.sub(r'(\s+|\(.*?\))', r'', cameraModel) if (cameraModel is not None) else r''
    except:
        cameraModel = r''
    if (len(cameraModel) == 0):
        try: software = EXIF.get(305, EXIF.get(11, r'')).lower()
        except: software = r''
        if (r'screenshot' in software): cameraModel = r'Screenshot from '
    try:
        date = EXIF.get(36867, EXIF.get(36868, EXIF.get(306, EXIF.get(29, r'')))).replace(r':', r'-')
    except:
        date = r''
    if (len(date) < 8):
        try:
            author = EXIF.get(315, EXIF.get(40093))
            if (isinstance(author, bytes)): author = author.decode(r'utf-8', r'ignore')
            author = (author + r' - ') if (author is not None) else r''
        except:
            author = r''
        try:
            title = EXIF.get(270, EXIF.get(40091))
            if (isinstance(title, bytes)): title = title.decode(r'utf-8', r'ignore')
        except:
            title = None
        if (not title): return os.path.split(currentName)[-1]
        return _normalized(author + title + os.path.splitext(currentName)[-1])
    else:
        _unmute()
        return _normalized(cameraModel + r' ' + date + os.path.splitext(currentName)[-1])

def songFilename( currentName, parsedInfo=None ):
    _mute()
    if (parsedInfo is None):
        try:
            parsedInfo = MediaInfo.parse(currentName)
        except:
            _unmute()
            return os.path.split(currentName)[-1]
    if (parsedInfo.tracks[0].overall_bit_rate is not None):
        bitrate = parsedInfo.tracks[0].overall_bit_rate
        if (bitrate > 1024): bitrate = str(int(bitrate // 1000)) + r' kbps'
        else: bitrate = str(int(bitrate)) + ' bps'
        bitrate = r' [' + bitrate + r']'
    else:
        bitrate = r''
    if (parsedInfo.tracks[0].track_name is not None): title = parsedInfo.tracks[0].track_name
    elif (parsedInfo.tracks[0].title is not None): title = parsedInfo.tracks[0].title
    else: title = r''
    if (parsedInfo.tracks[0].performer is not None): artist = parsedInfo.tracks[0].performer + r' - '
    elif (parsedInfo.tracks[0].composer is not None): artist = parsedInfo.tracks[0].composer + r' - '
    else: artist = r''
    if (parsedInfo.tracks[0].album is not None): album = parsedInfo.tracks[0].album + r' - '
    else: album = r''
    final = _normalized(artist + album + title + bitrate)
    _unmute()
    if (len(final) <= 1): return os.path.split(currentName)[-1]
    return (final + os.path.splitext(currentName)[-1])

def videoFilename( currentName, parsedInfo=None ):
    _mute()
    if (parsedInfo is None):
        try:
            parsedInfo = MediaInfo.parse(currentName)
        except:
            _unmute()
            return os.path.split(currentName)[-1]
    res = r''
    for track in parsedInfo.tracks:
        if (track.track_type[0] == r'V'):
            if (track.height is not None):
                if (track.height > 2000): res = r' [4K]'
                elif (track.height > 800): res = r' [1080p]'
                elif (track.height > 500): res = r' [720p]'
                elif (track.height > 380): res = r' [480p]'
                elif (track.height > 250): res = r' [360p]'
                break
    if (parsedInfo.tracks[0].movie_name is not None): title = parsedInfo.tracks[0].movie_name
    elif (parsedInfo.tracks[0].track_name is not None): title = parsedInfo.tracks[0].track_name
    elif (parsedInfo.tracks[0].title is not None): title = parsedInfo.tracks[0].title
    else: title = r''
    if (parsedInfo.tracks[0].performer is not None): artist = parsedInfo.tracks[0].performer + r' - '
    elif (parsedInfo.tracks[0].director is not None): artist = parsedInfo.tracks[0].director + r' - '
    elif (parsedInfo.tracks[0].composer is not None): artist = parsedInfo.tracks[0].composer + r' - '
    elif (parsedInfo.tracks[0].author is not None): artist = parsedInfo.tracks[0].author + r' - '
    elif (parsedInfo.tracks[0].writer is not None): artist = parsedInfo.tracks[0].writer + r' - '
    else: artist = r''
    final = _normalized(artist + title + res)
    _unmute()
    if ((len(artist) + len(title)) == 0):
        final = os.path.split(os.path.splitext(currentName)[0])[-1]
        final = _normalized(re.sub((r'( ?\[([0-9]{3,4}p|[48][Kk])\])+'), r'', final) + res)
    if (not final): return os.path.split(currentName)[-1]
    else: return (final + os.path.splitext(currentName)[-1])

def ambigMediaFilename( currentName ):
    try:
        parsedInfo = MediaInfo.parse(currentName)
        if (len(parsedInfo.video_tracks)):
            newName = videoFilename(currentName, parsedInfo)
            if (newName[-4:] == r'.ogg'): newName = newName[:-4] + r'.ogv'
            elif (newName[-4:] == r'.asf'): newName = newName[:-4] + r'.wmv'
            elif (newName[-5:] == r'.riff'): newName = newName[:-4] + r'.avi'
        else:
            newName = songFilename(currentName, parsedInfo)
            if (newName[-4:] == r'.mp4'): newName = newName[:-4] + r'.m4a'
            elif (newName[-4:] == r'.asf'): newName = newName[:-4] + r'.wma'
            elif (newName[-5:] == r'.riff'): newName = newName[:-5] + r'.wav'
            elif (newName[-3:] == r'.rm'): newName = newName[:-4] + r'.ra'
            elif (newName[-5:] == r'.rmvb'): newName = newName[:-5] + r'.ra'
        return newName
    except:
        return os.path.split(currentName)[-1]

def PDFFilename( currentName ):
    try:
        document = PDFFile(currentName, strict=False)
        if (document.isEncrypted): return os.path.split(currentName)[-1]
        info = document.documentInfo
        if (info is None): return os.path.split(currentName)[-1]
        author = info.get(r'/Author', r'')
        if (isinstance(author, PDFIndirectObject)): author = document.getObject(author)
        author = (author + r' - ') if (author is not None) else r''
        title = info.get(r'/Title', r'')
        if (isinstance(title, PDFIndirectObject)): title = document.getObject(title)
        if (not title): return os.path.split(currentName)[-1]
        return (_normalized(author + title) + r'.pdf')
    except:
        return os.path.split(currentName)[-1]

def OLEDocumentFilename( currentName ):
    try:
        document = OLEFile(currentName)
        documentMetadata = document.get_metadata()
        document.close()
        encoding = documentMetadata.codepage
    except:
        return os.path.split(currentName)[-1]
    encoding = r'cp' + str(encoding if ((encoding is not None) and (encoding > 0)) else 1252)
    author = r''
    if ((documentMetadata.author is not None) and (len(documentMetadata.author) > 1)):
        author = r' (' + documentMetadata.author.decode(encoding) + r')'
    if ((documentMetadata.title is not None) and (len(documentMetadata.title) > 1)):
        title = _normalized(documentMetadata.title.decode(encoding))
        return (_normalized(title + author) + os.path.splitext(currentName)[-1])
    return os.path.split(currentName)[-1]

def openXMLDocumentFilename( currentName ):
    try:
        document = ZIPFile(currentName, r'r')
        XMLMetadataFile = document.open(r'docProps/core.xml')
        parsedXML = _parsedXML(XMLMetadataFile)
        if (parsedXML is None): return os.path.split(currentName)[-1]
        field = parsedXML.find('//creator')
        author = (r' (' + field.text + r')') if (field is not None) else r''
        field = parsedXML.find('//title')
        if ((field is not None) and (len(field.text) > 1)): title = field.text
        else: return os.path.split(currentName)[-1]
        XMLMetadataFile.close()
        return (_normalized(title + author) + os.path.splitext(currentName)[-1])
    except:
        return os.path.split(currentName)[-1]

def openDocumentFilename( currentName ):
    try:
        with open(currentName, r'rb') as document:
            fileSignature = document.read(2)
            document.seek(0)
            if (fileSignature == b'<?'): parsedXML = _parsedXML(document)
            else: fileSignature = None
        if (fileSignature is None):
            XMLMetadataFile = ZIPFile(currentName, r'r').open(r'meta.xml')
            parsedXML = _parsedXML(XMLMetadataFile)
        if (parsedXML is None): return os.path.split(currentName)[-1]
        field = parsedXML.find(r'//initial-creator')
        if (not field): field = parsedXML.find(r'//creator')
        author = (r' (' + field.text + r')') if (field is not None) else r''
        field = parsedXML.find(r'//title')
        if ((field is not None) and (len(field.text) > 1)): title = field.text
        else: return os.path.split(currentName)[-1]
        return (_normalized(title + author) + os.path.splitext(currentName)[-1])
    except:
        return os.path.split(currentName)[-1]

def HTMLFilename( currentName ):
    try: xml = html.parse(currentName)
    except: return os.path.split(currentName)[-1]
    title = xml.find(r'.//title')
    if (title is None):
        title = xml.find(r'.//meta[@name="title"]')
        if (title is None): title = xml.find(r'.//meta[@property="og:title"]')
        if (title is None): title = xml.find(r'.//meta[@name="parsely-title"]')
        if (title is None): title = xml.find(r'.//name')
    if (title is not None): title = title.text
    else: return os.path.split(currentName)[-1]
    return (_normalized(title) + os.path.splitext(currentName)[-1])

def fontFilename( currentName ):
    try: font = ttLib.TTFont(currentName)
    except: return os.path.split(currentName)[-1]
    name = r''
    family = r''
    _mute()
    try:
        for record in font[r'name'].names:
            if (b'\x00' in record.string):
                name_str = record.string.decode(r'utf-16-be')
            else:
                try: name_str = record.string.decode(r'utf-8')
                except: name_str = record.string.decode(r'latin-1')
            if ((record.nameID == 2) and (not name)): name = name_str
            elif ((record.nameID == 1) and (not family)): family = name_str
            if (name and family): break
    except:
        _unmute()
        return os.path.split(currentName)[-1]
    path = currentName.rsplit(os.path.sep, 1)[0]
    name = _normalized(family + r' ' + name)
    _unmute()
    if (len(name) < 2): return os.path.split(currentName)[-1]
    return (name + r'.' + currentName.rsplit(r'.', 1)[-1])

def torrentFilename( currentName ):
    if (not os.path.isfile(currentName)): return os.path.split(currentName)[-1]
    with open(currentName, r'rb') as f:
        try: content = f.readline()
        except: return os.path.split(currentName)[-1]
        content = content.split(b'6:pieces')[0]
        try:
            encoding = cchardet.detect(content)[r'encoding']
            encoding = codecs.lookup(encoding if (encoding is not None) else r'utf-8').name
        except:
            encoding = r'utf-8'
        content = content.decode(encoding, r'ignore')
        name = re.findall(r'4:name([0-9]+):', content)
        if (not name): return os.path.split(currentName)[-1]
        name = re.findall(r'4:name' + name[0] + ':(.{' + name[0] + '})', content)
        if (not name): return os.path.split(currentName)[-1]
        path = currentName.rsplit(os.path.sep, 1)[0]
        return (_normalized(name[0]) + r'.torrent')

windowsPlaylistTitle = re.compile(r'<title>(.*)</title>')
def windowsPlaylistFilename( currentName ):
    title = None
    try:
        with open(currentName, r'rb') as f:
            title = windowsPlaylistTitle.findall(decodedFileContent(f))
            if ((len(title) > 0) and (len(title[0]) > 0)):
                title = windowsPlaylistTitle.sub(r'\1', title[0])
    except:
        pass
    if (not title): return os.path.split(currentName)[-1]
    else: return (_normalized(title) + r'.wpl')

def cueSheetFilename( currentName ):
    title = None
    try:
        with open(currentName, r'rb') as f:
            content = decodedFileContent(f)
            title = re.findall('\nTITLE \x22(.*)\x22', content)
            if ((len(title) == 0) or (len(title[0]) == 0)):
                title = re.findall('\nFILE \x22(.*)\.[a-zA-Z0-9+]{1,4}\x22', content)
                if ((len(title) > 0) and (len(title[0]) > 0)): title = title[0]
            else:
                title = title[0]
                artist = re.findall('\nPERFORMER \x22(.*)\x22', content)
                if ((len(artist) > 0) and (len(artist[0]) > 0)):
                    title = artist[0] + r' - ' + title
    except:
        pass
    if (not title): return os.path.split(currentName)[-1]
    else: return (_normalized(title) + r'.cue')

windowsRegistryFile = re.compile(r'.*\.(dat|hve|man|reg)(\.tmp)?$', re.IGNORECASE)
def windowsRegistryFilename( currentName ):
    try:
        regName = b'\x00' * 64
        REGEDIT4 = False
        with open(currentName, r'rb') as reg:
            regName = reg.read(112)
            if (regName[:8] == b'REGEDIT4'):
                REGEDIT4 = True
                reg.seek(0, 0)
                regName = decodedFileContent(reg)
        if (REGEDIT4):
            regName = [match[2:-2].rstrip(r']') for match in re.findall(r'\n\[[^\n]+\]\r?\n', regName)]
            regName = longestCommonPrefix(regName)
            if (regName.startswith(r'-')): regName = r'Clear ' + regName[1:]
        else:
            regName = regName[48:].decode(r'utf-16', r'ignore').strip('\x00?_- \n\\')
        if (len(regName) < 1): return os.path.split(currentName)[-1]
        if (not windowsRegistryFile.match(regName)): regName += r'.reg'
        return _normalized(re.sub(r'^([A-Z]):\\', r'\1_', regName).replace('\\', r'_'))
    except:
        return os.path.split(currentName)[-1]



# SPECIAL FILE MANIPULATION FUNCTIONS

removedJunkFiles = 0
def removeJunkFile( filePath ):
    try: os.remove(filePath)
    except FileNotFoundError: pass
    global removedJunkFiles
    removedJunkFiles += 1

def renameNotReplacing( file, newFilename ):
    if (file == newFilename): return file
    try:
        if (not os.path.exists(newFilename)):
            os.rename(file, newFilename)
            return newFilename
        else:
            i = 2
            name, ext = os.path.splitext(newFilename)
            while True:
                newFilename = name + r' (' + str(i) + r')' + ext
                if (not os.path.exists(newFilename)):
                    os.rename(file, newFilename)
                    return newFilename
                else:
                    i += 1
    except:
        return file

def moveNotReplacing( file, toWhere ):
    newFilename = os.path.join(toWhere, os.path.split(file)[-1].strip())
    return renameNotReplacing(file, newFilename)

renamedFiles = 0
def rename( filePath, newName, count=False ):
    if (len(newName) > 255):
        extension = os.path.splitext(newName)[-1]
        newName = newName[:(255 - len(extension))] + extension
    newName = os.path.join(os.path.split(filePath)[0], newName)
    try: newPath = renameNotReplacing(filePath, newName)
    except: return
    global renamedFiles
    if (count): renamedFiles += int(filePath != newPath)



# RENAMING LOOP FUNCTION

def renamingLoop( files, target, filenameFunction ):
    global done
    buffer = []
    if (isinstance(target, str)):
        def isTarget( filePath ): return files[i].endswith(target)
    elif (isinstance(target, re.Pattern)):
        def isTarget( filePath ): return target.match(files[i])
    else:
        return
    for i in range(0, len(files)):
        if (isTarget(files[i])):
            done += 1
            progress(r'Analyzing files...', done, initialTotal)
            rename(files[i], filenameFunction(files[i]), count=True)
        else:
            buffer.append(files[i])
    return buffer



# DEFINING FILENAME REGEXES

ddImageFile = re.compile(r'^.*\.(dd|e01|im[ag]|bin)$', re.IGNORECASE)

fontFile = re.compile(r'^.+\.(dfont|woff|[ot]t[cf]|tte)$')
codeFile = r'^.*\.([CcHh](\+\+|pp)?|[cejlrt]s|objc|[defmMPrRS]|p(y3?|[lm]|p|as|hp|s1)|s(h|ql|c(ala|ptd?)?)|'
codeFile += r'go|a(sp|d[bs])|c([bq]?l|lj[sc]?|ob(ra)?|py|yp)|li?sp|t(cl|bc)|j(ava|j)|(m|[eh]r)l|l?hs|'
codeFile += r'[rv]b|vhdl?|exs?|dart|applescript|f(or|90)|boo|[jt]sx|va(la|pi)|GAMBAS|(lit)?coffee|'
codeFile = re.compile(codeFile + 'fs([ix]|script)|jl|lua|mm|w?asm|hx(ml)?|g(v|roov)?y|w(l|at)|b(at|tm)|cmd)$')
pictureFile = r'^.*\.(a(n?i|png)|b([lm]p|pg)|d(c[rx]|ds|ib)|e(ps[fi]?|mf)|g(d|if)|i(mt?|co|cns)|flif|vsd|'
pictureFile += r'j(p[2efx]|[np]g|peg|xr)|m(ic|po|sp|ng)|p(c[dx]|ng|[abgnp]m|s[db])|odg|c(in|r2|rw|ur)|'
pictureFile = re.compile(pictureFile + r'[hw]dp|heic|s(gi|vgz?)|t(ga|iff?)|w(al|ebp|mf|bmp|pg)|x([bp]m|cf))$')
ambigMediaFile = re.compile(r'^.*\.(asf|ogg|webm|rm|riff|3g(p?[p2]|pp2))$')
videoFile = re.compile('^.*\.(avi|(fl|mq|vi|wm)v|m([4ko]v|p(4|e|e?g))|ogv|qt|rmvb)$')
documentFile = r'^.*\.((f?od|uo)[pst]|o(le|pf)|(xls|ppt|doc)x?|p(df|s|ps)|g(p[345x]?|tp)|tg|css|'
documentFile = re.compile(documentFile + r'e(nc|pub)|[a-z]?html?(\.gz)?|m(obi|d)|djvu?|chm|rtf|[tc]sv|dcx)$')
audioFile = r'^.*\.(m(4[abp]|ka|p[+c123]|idi?)|w(ma|a?v)|flac|a(ac|c3|pe|u)|dts|oga|tta|gsm|'
audioFile = re.compile(audioFile + r'ra|ofr|s(px|nd))$')

photorecName = re.compile(r'^(.*/)?f[0-9]{5,}(_[^/]*)?(\.[a-zA-Z0-9]+)?$')



# PROCESSING COMMAND LINE ARGUMENTS

if (r'-h' in sys.argv): helpMessage()

option_runningWithSudo = not os.getuid()

targetRootDir = None
photoRecTarget = None
commaSeparatedExtensions = re.compile(r'[a-zA-Z0-9][a-zA-Z0-9.+-]*(,[a-zA-Z0-9][a-zA-Z0-9.+-]*)*')
junkExtensions = r''
waitingPhotoRecArg = False
waitingRBFList = False
for arg in sys.argv:
    if (waitingPhotoRecArg):
        waitingRBFList = False
        if (arg.startswith(r'-')):
            photoRecTarget = r'_'
            photoRecTargetType = 0
        elif (stat.S_ISBLK(os.stat(arg).st_mode)):
            photoRecTargetType = 1
            photoRecTarget = arg
            continue
        elif (os.path.isfile(arg) and ddImageFile.match(arg)):
            photoRecTargetType = 2
            photoRecTarget = arg
            continue
        else:
            error("Invalid device or image: '" + arg + "'", 2)
    if (os.path.isdir(arg)):
        if (targetRootDir is None): targetRootDir = arg
        else: error("More than one path passed as argument", 2)
    elif (arg == '-x'):
        waitingPhotoRecArg = True
        import stat, subprocess
    elif (arg == '-r'):
        waitingRBFList = True
    elif (waitingRBFList):
        waitingRBFList = False
        if (commaSeparatedExtensions.match(arg)): junkExtensions += arg
        else: error("Invalid file extensions list: '" + arg + "'", 2)

if ((not targetRootDir) or (not os.path.isdir(targetRootDir))):
    if (photoRecTarget):
        try: os.mkdir(targetRootDir)
        except: error("No valid path specified", 2)
    else:
        error("No valid path specified", 2)

if (waitingRBFList): photoRecTarget = r'_'

if (option_runningWithSudo):
    uid = int(os.environ.get(r'SUDO_UID', os.getuid()))
    gid = int(os.environ.get(r'SUDO_GID', os.getgid()))
elif (photoRecTarget and (os.stat(photoRecTarget).st_uid != os.getuid())):
    error(("Cannot access '" + photoRecTarget + "' (try running as root)"), 1)

if (photoRecTarget):
    if (photoRecTarget == r'_'): command = [r'photorec', r'/log', r'/d', targetRootDir]
    else: command = [r'photorec', r'/log', r'/d', targetRootDir, photoRecTarget]
    try:
        with subprocess.Popen(command) as photoRecProc:
            photoRecProc.wait()
            if (photoRecProc.returncode and (len(os.listdir(targetRootDir)) == 0)):
                error("Could not run PhotoRec", photoRecProc.returncode)
        sys.stdout.write('\n')
    except OSError:
        error("Could not run PhotoRec", 1)

junkExtensions = [ext for ext in junkExtensions.split(r',') if (len(ext) > 0)]
junkExtensions = tuple([(ext if (ext.startswith(r'.')) else (r'.' + ext)) for ext in junkExtensions])
if (junkExtensions == (r'.',)): junkExtensions = ()
elif (len(junkExtensions) == 1): junkExtensions = junkExtensions[0]

if (r'-Q' in sys.argv):
    def progress( message, done, total ): pass
if (r'-q' in sys.argv):
    def progress( message, done, total ): pass
    def print( *args ): pass
    def _unmute(): sys.stderr = sys.__stderr__
    sys.stdout = open(os.devnull, r'w')

option_removeKnownJunk = r'-J' not in sys.argv
if (not option_removeKnownJunk):
    def removeJunkFile( filePath ): pass

option_dedupAcrossExtensions = r'-d' in sys.argv
option_removeDuplicates = r'-D' not in sys.argv
option_keepEmptyFiles = r'-z' in sys.argv
option_keepDirStructure = r'-k' in sys.argv
option_photorecNamesOnly = r'-n' in sys.argv



# GENERATING THE LIST OF FILES TO BE PROCESSED

sys.stdout.write(r'Listing files...')
files = []
for path, subdirs, items in os.walk(targetRootDir):
    files += [os.path.join(path, name) for name in items]
if (option_dedupAcrossExtensions):
    files = [(os.stat(file).st_size, None, file) for file in files]
else:
    files = [(os.stat(file).st_size, os.path.splitext(file)[-1], file) for file in files]
initialTotal = len(files)
if (option_photorecNamesOnly):
    files = [(size, ext, file) for size, ext, file in files if photorecName.match(file)]
files = sorted(files)
if (initialTotal == 1): print('\r1 file found' + (r' ' * 50) + ('\b' * 50))
else: print('\r' + _num(initialTotal) + ' files found' + (r' ' * 20) + ('\b' * 20))



# REMOVING EMPTY FILES

sys.stdout.write(r'Removing empty files...')
j = 0
if ((not option_keepEmptyFiles) and (files[0][0] == 0)):
    for i in range(0, len(files)):
        if (files[i][0] != 0): break
        j += 1
    for i in range(0, j):
        progress(r'Removing empty files...', (j - (j - i)), j)
        try: os.remove(files[i][2])
        except FileNotFoundError: pass
    files = files[j:]
    initialTotal -= j
if (j == 1): print('\r1 empty file removed' + (r' ' * 50) + ('\b' * 50))
else: print('\r' + _num(j) + ' empty files removed' + (r' ' * 20) + ('\b' * 20))



# DEDUPLICATING FILES

if (option_removeDuplicates):
    sys.stdout.write(r'Deduplicating files...')
    done = 0
    actuallyDeduped = 0
    for i in range(0, len(files)):
        if (files[i][0] == 0): continue
        for j in range((i + 1), len(files)):
            if (files[i][0] != files[j][0]): break
            if (files[i][1] == files[j][1]):
                if (not os.path.exists(files[i][2])):
                    files[j] = (-1, r'/', files[i][2])
                    break
                if (not os.path.exists(files[j][2])):
                    done += 1
                    files[j] = (-1, r'/', files[j][2])
                    continue
                if (filecmp.cmp(files[i][2], files[j][2], shallow=False)):
                    actuallyDeduped += 1
                    progress(r'Deduplicating files...', (actuallyDeduped + done), initialTotal)
                    os.remove(files[j][2])
                    files[j] = (-1, r'/', files[j][2])
        done += 1
        progress(r'Deduplicating files...', (actuallyDeduped + done), initialTotal)
    initialTotal -= actuallyDeduped
    if (actuallyDeduped == 1): print('\r1 duplicate removed' + (r' ' * 50) + ('\b' * 50))
    else: print('\r' + _num(actuallyDeduped) + ' duplicates removed' + (r' ' * 20) + ('\b' * 20))



# STARTING TO PROCESS FILES

if (option_photorecNamesOnly):
    files = sorted([file for size, ext, file in files if ((size > 0) and photorecName.match(file))])
else:
    files = sorted([file for size, ext, file in files if (size > 0)])
sys.stdout.write(r'Analyzing files...')
done = 0



# REMOVING JUNK FILES

if (option_removeKnownJunk):
    for file in files:
        if (file.endswith(r'.pyc')):
            os.remove(file)
            done += 1
        progress(r'Analyzing files...', done, initialTotal)
    files = [file for file in files if (not file.endswith(r'pyc'))]

    files = removeFilesContaining(files, r'.xml', b'<!-- Created automatically by update-mime-database')
    done = initialTotal - len(files)
    progress(r'Analyzing files...', done, initialTotal)
    files = removeFilesContaining(files, r'.html', b'\n<!-- Generated by javadoc')
    done = initialTotal - len(files)
    progress(r'Analyzing files...', done, initialTotal)
    files = removeFilesContaining(files, r'.c', b'\n#define _GLIBCXX_')
    done = initialTotal - len(files)
    progress(r'Analyzing files...', done, initialTotal)
    files = removeFilesContaining(files, r'.c', b'\n#define _BOOST_')
    done = initialTotal - len(files)
    progress(r'Analyzing files...', done, initialTotal)

    removedJunkFiles += done



# IMPROVING SOME FILENAMES PHOTOREC SOMETIMES PROVIDES

prenamedFile1 = r'^f[0-9]{5,}_([^_].*)[._](([dr]ll|exe|sys)(_mui)?|'
prenamedFile1 = re.compile(prenamedFile1 + r'd2s|ocx)$', re.IGNORECASE)
prenamedFile2 = r'^f[0-9]{5,}_([^_].*)[._](zip|pdf|doc|xls|'
prenamedFile2 = re.compile(prenamedFile2 + r'pp[st])$', re.IGNORECASE)
def fixedPhotoRecName1( match ):
    return (match.group(1) + r'.' + match.group(2).lower().replace(r'_', r'.'))
def fixedPhotoRecName2( match ):
    return (re.sub(r'\s+', r' ', match.group(1).replace(r'_', r' ')).strip() + r'.' +
            match.group(2).lower().replace(r'_', r'.'))
buffer = []
for i in range(0, len(files)):
    filename = files[i].rsplit(os.path.sep, 1)[-1]
    if (prenamedFile1.match(filename)):
        done += 1
        progress(r'Analyzing files...', done, initialTotal)
        rename(files[i], prenamedFile1.sub(fixedPhotoRecName1, filename), count=True)
    elif (prenamedFile2.match(filename)):
        done += 1
        progress(r'Analyzing files...', done, initialTotal)
        rename(files[i], prenamedFile2.sub(fixedPhotoRecName2, filename), count=True)
    else:
        buffer.append(files[i])
files = buffer



# REMOVING UNSUPPORTED FILES FROM THE LIST

unsupported = r'^.*\.(d2s|sys|[ao]|json|class|m3u|log|'
unsupported = re.compile(unsupported + r'pyc)$')
files = [file for file in files if (not unsupported.match(file))]
done = initialTotal - len(files)
progress(r'Analyzing files...', done, initialTotal)



# NAMING PLAIN TEXT FILES

logLine1 = r'(^|\n)(19|2[01])[0-9]{2}-(0[1-9]|1[012])-([012][0-9]|3[01])[\t ]'
logLine1 = re.compile(logLine1 + r'[0-9][0-9]:[0-9][0-9]:[0-9][0-9]')
logLine2 = re.compile(r'(^|\n)\[([01][0-9]|2[0-4]):([0-5][0-9]|60):([0-5][0-9]|60)\.[0-9]{3}')
logLine3 = r'(^|\n)\[(19|2[01])[0-9]{2}-?(0[1-9]|1[012])-?([012][0-9]|3[01])[\t ]([01][0-9]|2[0-4])'
logLine3 = re.compile(logLine3 + ':([0-5][0-9]|60):([0-5][0-9]|60)\.[0-9]{3}\]')
xmlLine = re.compile(r'(^|\n)[\t ]*<')
tclLine = re.compile(r'(^|\n)(#+ -\*- tcl -\*-|package require Tcl)')
srtTime = r'\r?\n\r?\n[0-9]+\r?\n[0-9]{2}:[0-9]{2}:[0-9]{2},[0-9]{3} --> '
srtTime = re.compile((srtTime + r'[0-9]{2}:[0-9]{2}:[0-9]{2},[0-9]{3}'), re.MULTILINE)
gpd_pcfNameLine = re.compile(r'\n\*(PC|GPD)FileName:[\t ]*\x22(.*\.[GgPp][Pp][Dd])\x22')
windowsJunkXMLLine = re.compile('<(assemblyIdentity|component) name=\x22Microsoft-Windows-')
maybeJSON = re.compile(r'^\s*[\[{]')
buffer = []
for i in range(0, len(files)):
    if (files[i].endswith(r'.txt') and os.path.isfile(files[i])):
        with open(files[i], r'rb') as f:
            content = decodedFileContent(f)
            lineCount = content.count('\n')
            if ((lineCount > 6) and
                ((len(logLine1.findall(content)) >= (lineCount - 1)) or
                (len(logLine2.findall(content)) >= (lineCount - 1)) or
                (len(logLine3.findall(content)) >= (lineCount - 1)))):
                rename(files[i], (os.path.split(files[i])[-1][:-4] + r'.log'))
                done += 1
            elif (content.startswith(r'<?xml')):
                rename(files[i], (os.path.split(files[i])[-1][:-4] + r'.xml'))
                buffer.append(files[i][:-4] + r'.xml')
            elif (len(srtTime.findall(content)) > max(1, (lineCount / 8))):
                rename(files[i], (os.path.split(files[i])[-1][:-4] + r'.srt'))
                buffer.append(files[i][:-4] + r'.srt')
            elif ((r'<!-- Created with Inkscape (http://www.inkscape.org/) -->' in content) and
                (r'</svg>' in content)):
                rename(files[i], (os.path.split(files[i])[-1][:-4] + r'.svg'))
                buffer.append(files[i][:-4] + r'.svg')
            elif (len(tclLine.findall(content)) > 0):
                rename(files[i], (os.path.split(files[i])[-1][:-4] + r'.tcl'))
                buffer.append(files[i][:-4] + r'.tcl')
            else:
                done += 1
                if (maybeJSON.match(content)):
                    try:
                        junk = json.loads(content)
                        rename(files[i], (os.path.split(files[i])[-1][:-4] + r'.json'))
                        del junk
                        continue
                    except:
                        pass
                gpd_pcfName = gpd_pcfNameLine.findall(content)
                if (len(gpd_pcfName) == 1):
                    newFilename = _normalized(gpd_pcfName[0][1])
                    newFilename = re.sub(r'(\.[GgPp][Pp][Dd])$', lambda x: x.group(0).lower(), newFilename)
                    rename(files[i], newFilename)
                    continue
                elif (((lineCount > 6) and (len(xmlLine.findall(content)) >= (lineCount - 1)) and
                      (len(windowsJunkXMLLine.findall(content)) > (lineCount / 6))) or
                      (len(set(content)) < min(12, round(len(content) / 2))) or
                      (content.startswith(r'# Autogenerated by Sphinx'))):
                    removeJunkFile(files[i])
        progress(r'Analyzing files...', done, initialTotal)
    else:
        buffer.append(files[i])
files = buffer

ssaLine = re.compile(r'(^|\n)Dialogue: [0-9]+,[0-9]+:([0-5][0-9]|60):([0-5][0-9]|60)\.[0-9]{2}')
desktopEntryNameLine1 = re.compile(r'\nExec=([^\n\t ]+)')
desktopEntryNameLine2 = re.compile(r'\nName=([^\n#]*)')
buffer = []
for i in range(0, len(files)):
    if (files[i].endswith(r'.ini') and os.path.isfile(files[i])):
        with open(files[i], r'rb') as f:
            content = decodedFileContent(f)
            lineCount = content.count('\n')
            if (content.startswith(r'[Script Info]')):
                if (len(ssaLine.findall(content)) > max(1, ((lineCount / 3) - 25))):
                    rename(files[i], (os.path.split(files[i])[-1][:-4] + r'.ass'))
                    buffer.append(files[i][:-4] + r'.ass')
                else:
                    buffer.append(files[i])
            elif (content.startswith(r'[General]\s*\n\s*Version=DrumSynth v2\.0')):
                rename(files[i], (os.path.split(files[i])[-1][:-4] + r'.ds'))
                done += 1
            elif (content.startswith((r'[MIME Cache]', r'[.ShellClassInfo]'))):
                removeJunkFile(files[i])
            elif (content.startswith(r'[Device Install Log]')):
                rename(files[i], (os.path.split(files[i])[-1][:-4] + r'.log'))
            elif (content.startswith(r'[Desktop Entry]')):
                newFilename = desktopEntryNameLine1.findall(content)
                if (len(newFilename) < 1):
                    newFilename = desktopEntryNameLine2.findall(content)
                    if (len(newFilename) < 1): newFilename = os.path.split(files[i])[-1][:-4]
                    else: newFilename = _normalized(re.sub(r'\s+', r'-', newFilename[0].lower()))
                else:
                    newFilename = _normalized(os.path.split(newFilename[0])[-1])
                rename(files[i], (newFilename + r'.desktop'), count=True)
                done += 1
            else:
                done += 1
        progress(r'Analyzing files...', done, initialTotal)
    else:
        buffer.append(files[i])
files = buffer



# NAMING CODE FILES

className = re.compile(r'\n[\t ]*public +(static +)?class ([a-zA-Z0-9_]+)')
packageName = re.compile(r'\n[\t ]*package ([a-zA-Z0-9_]+);')
variableName = r'^[a-zA-Z_][a-zA-Z0-9_]*'
cppLine = r'((^|\n)[\t ]*(namespace\s*' + variableName + '\s*\{|class\s*' + variableName
cppLine += r'\s*[;:{]|#include <[^<>]*([^.][^h]|\.hpp)>|cout\s*<<|cin\s*>>|template\s*<[^\n;]*>)|'
cppLine = re.compile(cppLine + '::|\x22\x22_' + variableName + r')')
cComments = re.compile(r'(//.*?\n|/\*.*?\*/)')
cStrings = re.compile('(\x22.*?[^\\\\]\x22|\x27.*?[^\\\\]\x27)')
buffer = []
for i in range(0, len(files)):
    if (files[i].endswith(r'.java')):
        with open(files[i], r'rb') as f:
            content = decodedFileContent(f)
            csharp = re.findall(r'^using +[a-zA-Z0-9_.]+;', content)
            if (len(csharp) > 0):
                rename(files[i], (os.path.split(files[i])[-1][:-5] + r'.cs'))
                files[i] = files[i][:-5] + r'.cs'
    elif (files[i].endswith(r'.c')):
        with open(files[i], r'rb') as f:
            content = cStrings.sub('\x22\x22', cComments.sub(r'', decodedFileContent(f)))
            if (len(cppLine.findall(content)) > 0):
                rename(files[i], (os.path.split(files[i])[-1][:-5] + r'.cpp'))
                files[i] = files[i][:-5] + r'.cpp'
    if (files[i].endswith((r'.cs', r'java'))):
        done += 1
        progress(r'Analyzing files...', done, initialTotal)
        with open(files[i], r'rb') as f:
            content = decodedFileContent(f)
            pkg = packageName.findall(content)
            name = className.findall(content)
            if (len(name) != 1): continue
            newFilename = _normalized(name[0][1]) + os.path.splitext(files[i])[-1]
            if (len(pkg) == 1): newFilename = _normalized(pkg[0]) + r'.' + newFilename
            rename(files[i], newFilename, count=True)
    else:
        buffer.append(files[i])
files = buffer



# NAMING IMAGE FILES

files = renamingLoop(files, pictureFile, imageFilename)



# NAMING MEDIA FILES

files = renamingLoop(files, r'.mp4', ambigMediaFilename)
files = renamingLoop(files, ambigMediaFile, ambigMediaFilename)
files = renamingLoop(files, audioFile, songFilename)
files = renamingLoop(files, videoFile, videoFilename)



# NAMING DOCUMENT FILES

files = renamingLoop(files, r'.pdf', PDFFilename)
files = renamingLoop(files, re.compile(r'^.+\.(doc|xls|ppt|ole)$'), OLEDocumentFilename)
files = renamingLoop(files, re.compile(r'^.+\.(doc|xls|ppt)x$'), openXMLDocumentFilename)
files = renamingLoop(files, re.compile(r'^.+\.f?od[gpst]$'), openDocumentFilename)
files = renamingLoop(files, re.compile(r'^.+\.[a-z]?html?$'), HTMLFilename)



# NAMING ARCHIVES AND COMPRESSED FILES

buffer = []
for i in range(0, len(files)):
    if (files[i].endswith(r'.html.gz')):
        done += 1
        progress(r'Analyzing files...', done, initialTotal)
        try: xml = html.fromstring(gzip.open(files[i], r'rb').read())
        except: continue
        title = xml.find(r'.//title')
        if (title is None):
            title = xml.find(r'.//meta[@name="title"]')
            if (title is None): title = xml.find(r'.//meta[@property="og:title"]')
            if (title is None): title = xml.find(r'.//meta[@name="parsely-title"]')
            if (title is None): title = xml.find(r'.//name')
        if (title is not None): title = title.text
        else: continue
        rename(files[i], (_normalized(title) + r'.html.gz'), count=True)
    elif (files[i].endswith(r'.gz')):
        try:
            gz = gzip.open(files[i], r'rb')
        except:
            removeJunkFile(files[i])
            print (files[i] + " :: dead .gz") #TODO
    else:
        buffer.append(files[i])
files = buffer



# NAMING FONT FILES

files = renamingLoop(files, fontFile, fontFilename)



# NAMING TORRENT FILES

files = renamingLoop(files, r'.torrent', torrentFilename)



# NAMING PLAYLIST AND CUE FILES

files = renamingLoop(files, r'.wpl', windowsPlaylistFilename)
files = renamingLoop(files, r'.cue', cueSheetFilename)



# NAMING WINDOWS REGISTRY FILES

files = renamingLoop(files, r'.reg', windowsRegistryFilename)



# SOME VERBOSITY

if (done == 1): print('\r1 file analyzed' + (r' ' * 50) + ('\b' * 50))
else: print('\r' + _num(done) + ' files analyzed' + (r' ' * 20) + ('\b' * 20))
if (renamedFiles == 1): print('1 file renamed')
else: print(_num(renamedFiles) + ' files renamed')
if (removedJunkFiles == 1): print('1 junk file removed')
else: print(_num(removedJunkFiles) + ' junk files removed')



# REMOVING FILES BY EXTENSION (IF SPECIFIED)

if (len(junkExtensions) > 0):
    done = 0
    if (option_photorecNamesOnly):
        def isValidJunkByExtension( filename ):
            return (filename.endswith(junkExtensions) and photorecName.match(filename))
    else:
        def isValidJunkByExtension( filename ):
            return filename.endswith(junkExtensions)
    for path, subdirs, items in os.walk(targetRootDir):
        for name in items:
            if (isValidJunkByExtension(name)):
                done += 1
                progress(r'Removing files by extension...', done, initialTotal)
                removeJunkFile(os.path.join(path, name))
    if (done == 1): print('\r1 file removed by extension' + (r' ' * 30) + ('\b' * 30))
    else: print('\r' + _num(done) + ' files removed by extension' + (r' ' * 20) + ('\b' * 20))



# CREATING MORE MEANINGFUL SUBDIRECTORIES

if (not option_keepDirStructure):
    audioSubdir = os.path.join(targetRootDir, r'Audio')
    try: os.mkdir(audioSubdir)
    except: pass
    documentsSubdir = os.path.join(targetRootDir, r'Documents')
    try: os.mkdir(documentsSubdir)
    except: pass
    fontsSubdir = os.path.join(targetRootDir, r'Fonts')
    try: os.mkdir(fontsSubdir)
    except: pass
    picturesSubdir = os.path.join(targetRootDir, r'Pictures')
    try: os.mkdir(picturesSubdir)
    except: pass
    videosSubdir = os.path.join(targetRootDir, r'Videos')
    try: os.mkdir(videosSubdir)
    except: pass
    txtSubdir = os.path.join(targetRootDir, r'Plain Text')
    try: os.mkdir(txtSubdir)
    except: pass
    codeSubdir = os.path.join(targetRootDir, r'Code')
    try: os.mkdir(codeSubdir)
    except: pass
    miscSubdir = os.path.join(targetRootDir, r'Misc')
    try: os.mkdir(miscSubdir)
    except: pass



# SORTING FILES INTO MORE MEANINGFUL SUBDIRECTORIES

if (not option_keepDirStructure):
    sys.stdout.write(r'Organizing files...')
    done = 0
    files = []
    for path, subdirs, items in os.walk(targetRootDir):
        files += [os.path.join(path, name) for name in items]
    initialTotal = len(files)
    for file in files:
        if (ambigMediaFile.match(file)):
            av = MediaInfo.parse(file)
            audioOnly = True
            for track in av.tracks:
                if (track.track_type[0] == r'V'):
                    audioOnly = False
                    break
            if (audioOnly): files[done] = moveNotReplacing(file, audioSubdir)
            else: files[done] = moveNotReplacing(file, videosSubdir)
        else:
            if (file.endswith(r'txt')): files[done] = moveNotReplacing(file, txtSubdir)
            elif (fontFile.match(file)): files[done] = moveNotReplacing(file, fontsSubdir)
            elif (videoFile.match(file)): files[done] = moveNotReplacing(file, videosSubdir)
            elif (audioFile.match(file)): files[done] = moveNotReplacing(file, audioSubdir)
            elif (documentFile.match(file)): files[done] = moveNotReplacing(file, documentsSubdir)
            elif (pictureFile.match(file)): files[done] = moveNotReplacing(file, picturesSubdir)
            elif (codeFile.match(file)): files[done] = moveNotReplacing(file, codeSubdir)
            else: files[done] = moveNotReplacing(file, miscSubdir)
        done += 1
        progress(r'Organizing files...', done, initialTotal)

    if (done == 1): print('\r1 file moved' + (r' ' * 50) + ('\b' * 50))
    else: print('\r' + _num(done) + ' files moved' + (r' ' * 20) + ('\b' * 20))



# FURTHER SPLITTING FILES INTO SUB-SUBDIRECTORIES

if (not option_keepDirStructure):
    sys.stdout.write(r'Splitting files into subdirectories...')
    done = 0
    j = 0
    maxFilesPerDir = 250
    for subdir in [os.path.join(targetRootDir, d) for d in os.listdir(targetRootDir)]:
        files = [os.path.join(subdir, file) for file in os.listdir(subdir)]
        files = [file for file in files if os.path.isfile(file)]
        if (len(files) <= maxFilesPerDir):
            done += len(files)
            continue
        files = split(sorted(files, key=lambda x: os.stat(x).st_size), maxFilesPerDir)
        i = 0
        j += 1
        for chunk in files:
            i += 1
            subsubdir = os.path.join(subdir, str(i))
            try:
                os.mkdir(subsubdir)
            except FileExistsError:
                if (not os.path.isdir(subsubdir)): continue
            except:
                continue
            for file in chunk:
                os.rename(file, os.path.join(subsubdir, os.path.split(file)[-1]))
                done += 1
                progress(r'Splitting files into subdirectories...', done, initialTotal)

    if (done < maxFilesPerDir):
        sys.stdout.write('\r' + (r' ' * 75) + '\r')
    else:
        sys.stdout.write('\r' + _num(done) + ' files split into ' _num(j) + ' subdirectories')
        print((r' ' * 20) + ('\b' * 20))



# REMOVING EMPTY SUBDIRECTORIES LEFT BEHIND

for path, subdirs, items in os.walk(targetRootDir):
    try: os.rmdir(path)
    except: pass



# FIXING FILE OWNERSHIPS IF RUNNING AS ROOT

if (option_runningWithSudo):
    sys.stdout.write('Fixing ownership of files and directories...')
    for path, subdirs, items in os.walk(targetRootDir):
        for name in items: os.chown(os.path.join(path, name), uid, gid)
        for name in subdirs: os.chown(os.path.join(path, name), uid, gid)



# DONE

print('\rDone!' + (r' ' * 70))
