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

import sys, os, stat, re, mmap, codecs, json, gzip, filecmp, time, warnings
from multiprocessing import Pool, Value as SharedValue
from unicodedata import category as ucategory, normalize as unormalize
from zipfile import ZipFile as ZIPFile, BadZipFile as BadZipFileError
from zlib import error as ZLibError

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

Example: """ + command + """ -r log,xml,pyc -m 300 -n -I /path/to/recup_dir

 Options:

  -h        Display this help message and exits
  -D        Do not remove duplicate files
  -d        Ignore file extension when deduplicating files
  -I        Remove duplicate images (visual duplicates) (largest ones kept)
  -J        Do not remove junk files (well known to be usually unwanted)
  -K        Keep directory structure (move no files, remove no directories)
  -k        Keep files where they are, but remove empty directories
  -m NUM    Set maximum files per directory to NUM (default = 250)
  -N        Do not rename any file
  -n        Only rename/remove files with photorec-generated names
  -Q        No real-time progress information
  -q        Quiet mode (no verbosity)
  -r EXTS   Remove files with any of the given (comma-separated) extension(s)
  -T        Remove duplicate txts (textual duplicates)
  -x [DEV]  Run PhotoRec on DEV (device or image path) before anything else
  -z        Do not remove empty (0B) files

"""
    sys.__stdout__.write(message)
    exit(0)

def error( message, whatToReturn ):
    sys.stderr.write('\x1B[31;1mError: ' + message + '\n')
    sys.stderr.flush()
    exit(whatToReturn)

def progress( message, done, total ):
    progressLen = (len(str(total)) * 2) + 1
    p = '\x1B[2m' + str(done) + ((r'/' + str(total)) if total else r'') + '\x1B[0m'
    print(('\r' + message + r' ' + p.ljust(progressLen)), end=r'', flush=True)
    print(('\b' * (progressLen - len(p))), end=r'', flush=True)

def _clearLine():
    print('\r' + (r' ' * 80) + '\r', end=r'', flush=True)

def _num( x ):
    return (str(x) if (x > 0) else r'No')

def _unmute():
    sys.stderr = sys.__stderr__
    sys.stdout = sys.__stdout__

def _mute():
    try: sys.stderr = sys.stdout = open(os.devnull, r'w')
    except: _unmute()

def formatedDuration( duration ):
    hours = int(duration) // 3600
    minutes = int(duration % 3600) // 60
    seconds = round(duration % 60, (3 if (duration >= 1) else 6))
    time = ((str(minutes) + 'm ') if minutes else r'') + str(seconds) + r's'
    if (hours): time = str(hours) + 'h ' + time
    return time

def stepConclusion( message, done, duration ):
    _clearLine()
    message = message.replace(r'#', _num(done))
    if (done and (duration >= 0.01)):
        message += ' in ' + formatedDuration(duration)
    print(message.replace(r'_', (r'' if (initialTotal == 1) else r's')) + '\n', end=r'', flush=True)



# UTILITY FUNCTION

def longestCommonPrefix( stringList ):
    if (not stringList): return r''
    shortest = min(stringList, key=len)
    for i, currentChar in enumerate(shortest):
        for other in stringList:
            if (other[i] != currentChar): return shortest[:i]
    return shortest

def split( l, chunkSize ):
    buffer = []
    for i in range(0, len(l), chunkSize):
        buffer.append(l[i:(i + chunkSize)])
    return buffer



# TEXT NORMALIZATION AND DECODING FUNCTIONS

_ucats = {r'Cc', r'Cf', r'Co', r'Cs'}
_table = dict.fromkeys(i for i in range(sys.maxunicode) if (ucategory(chr(i)) in _ucats))
_table = { cat:r' ' for cat in _table}
_tablex = _table
_tablex[ord('\n')] = r' '
_tablex[ord('\r')] = r' '
_tablex[ord(r'?')] = r' '
_tablex[ord(r'*')] = r' '
_tablex[ord('\x22')] = '\x27\x27'
_tablex[ord(r'/')] = r' - '
_tablex[ord('\\')] = r' - '
_tablex[ord(r':')] = r' - '
_tablex[ord(r'|')] = r' - '
_tablex[ord(r'<')] = r'('
_tablex[ord(r'>')] = r')'

def normalizedText( stringOrStrings ):
    if (not stringOrStrings):
    	return r''
    elif (isinstance(stringOrStrings, list)):
        return [normalizedText(string) for string in stringOrStrings]
    elif (isinstance(stringOrStrings, dict)):
        return dict((key, normalizedText(string)) for key, string in stringOrStrings.items())
    normalized = unormalize(r'NFC', stringOrStrings.translate(_table)).strip()
    return re.sub(r'\s+', r' ', normalized)

def normalizedFilename( stringOrStrings ):
    if (not stringOrStrings):
    	return r''
    elif (isinstance(stringOrStrings, list)):
        return [normalizedFilename(string) for string in stringOrStrings]
    elif (isinstance(stringOrStrings, dict)):
        return dict((key, normalizedFilename(string)) for key, string in stringOrStrings.items())
    normalized = unormalize(r'NFC', stringOrStrings.translate(_tablex)).strip()
    return re.sub(r'\s+', r' ', re.sub(r'^- ', r'', re.sub(r'( - )+', r' - ', normalized)))

_codecAliases = {r'cp10000':r'mac_roman', r'cp1281':r'mac_turkish', r'cp1286':r'mac_iceland'}

def encodingName( knownName ):
    try:
        enc = codecs.lookup(_codecAliases.get(knownName, knownName))
        return enc.name
    except LookupError:
        return r'cp1252'



# SPECIAL FILE MANIPULATION FUNCTIONS

def fileSize( filePath ):
    try: size = os.stat(filePath).st_size
    except: size = 0
    return size

def removeFile( filePath ):
    try: os.remove(filePath)
    except FileNotFoundError: pass
    except PermissionError: return

removedJunkFiles = 0
def removeJunkFile( filePath ):
    try: os.remove(filePath)
    except FileNotFoundError: pass
    except PermissionError: return
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
    newPath = renameNotReplacing(filePath, newName)
    global renamedFiles
    if (count): renamedFiles += int(filePath != newPath)

extensionsChanged = 0
def changeExtension( filePath, currentExtensionLength, newExtension, count=False ):
    newPath = os.path.split(files[i])[-1][:-currentExtensionLength] + newExtension
    rename(filePath, newPath)
    global extensionsChanged
    if (count): extensionsChanged += int(filePath != newPath)
    return newPath

def createSubdirs( rootDirPath, subdirs ):
    subdirPaths = [rootDirPath] * len(subdirs)
    for i in range(len(subdirs)):
        subdirPath = os.path.join(rootDirPath, subdirs[i])
        try: os.mkdir(subdirPath)
        except FileExistsError: pass
        except: continue
        subdirPaths[i] = subdirPath
    return tuple(subdirPaths)



# XML PARSING FUNCTION

def parsedXML( file ):
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
    for i in range(len(files)):
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
        encoding = encodingName(encoding)
    except:
        encoding = r'utf-8'
    content = content.decode(encoding, r'ignore')
    return content.strip()



# JUNK DETECTION FUNCTIONS

def isBadGZ( gzFilePath ):
    try:
        with gzip.open(gzFilePath) as gz:
            while gz.read(262144): pass
    except (IOError, EOFError, ZLibError):
        return True
    except:
        return False
    return False

def isBadZIP( zipFilePath ):
    try: z = ZIPFile(zipFilePath)
    except (BadZipFileError): return True
    except: return False
    return False

def isBadImage( imagePath ):
    try: i = Image.open(imagePath)
    except: return False
    try: i.load()
    except OSError: return True
    except: return False



# METADATA-TO-FILENAME FUNCTIONS

className = re.compile(r'\n[\t ]*public +((abstract|static) +)*class ([a-zA-Z0-9_]+)')
packageName = re.compile(r'\n[\t ]*package ([a-zA-Z0-9_]+);')
def javaCSharpFilename( currentPath ):
    try:
        with open(currentPath, r'rb') as f:
            content = decodedFileContent(f)
            pkg = packageName.findall(content)
            name = className.findall(content)
        if (len(name) != 1): return os.path.split(currentPath)[-1]
        newFilename = normalizedFilename(name[0][2]) + os.path.splitext(currentPath)[-1]
        if (len(pkg) == 1): newFilename = normalizedFilename(pkg[0]) + r'.' + newFilename
        return newFilename
    except:
        return os.path.split(currentPath)[-1]

def nonEXIFImageFilename( currentPath, imageInfo ):
    date = imageInfo.get(r'Creation Time', r'').replace(r':', r'-')
    isScreenshot = r'screenshot' in imageInfo.get(r'Software', r'').lower()
    title = r''
    author = r''
    return os.path.split(currentPath)[-1]

def imageFilename( currentPath ):
    try: image = Image.open(currentPath, r'r')
    except: return os.path.split(currentPath)[-1]
    try: EXIF = image._getexif()
    except: EXIF = None
    if (not EXIF):
        try:
            image.load()
            EXIF = image.info.get(r'exif', None) #TODO: must parse it into a dict()
        except:
            return os.path.split(currentPath)[-1]
        if (not EXIF):
            newFilename = nonEXIFImageFilename(currentPath, image.info)
            image.close()
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
        if (not title): return os.path.split(currentPath)[-1]
        return normalizedFilename(author + title + os.path.splitext(currentPath)[-1])
    else:
        return normalizedFilename(cameraModel + r' ' + date + os.path.splitext(currentPath)[-1])

def songFilename( currentPath, parsedInfo=None ):
    _mute()
    if (parsedInfo is None):
        try:
            parsedInfo = MediaInfo.parse(currentPath)
        except:
            _unmute()
            return os.path.split(currentPath)[-1]
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
    final = normalizedFilename(artist + album + title + bitrate)
    _unmute()
    if (len(final) <= 1): return os.path.split(currentPath)[-1]
    return (final + os.path.splitext(currentPath)[-1])

def videoFilename( currentPath, parsedInfo=None ):
    _mute()
    if (parsedInfo is None):
        try:
            parsedInfo = MediaInfo.parse(currentPath)
        except:
            _unmute()
            return os.path.split(currentPath)[-1]
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
    final = normalizedFilename(artist + title + res)
    _unmute()
    if ((len(artist) + len(title)) == 0):
        final = os.path.split(os.path.splitext(currentPath)[0])[-1]
        final = normalizedFilename(re.sub((r'( ?\[([0-9]{3,4}p|[48][Kk])\])+'), r'', final) + res)
    if (not final): return os.path.split(currentPath)[-1]
    else: return (final + os.path.splitext(currentPath)[-1])

def ambigMediaFilename( currentPath ):
    try:
        parsedInfo = MediaInfo.parse(currentPath)
        if (len(parsedInfo.video_tracks)):
            newName = videoFilename(currentPath, parsedInfo)
            if (newName[-4:] == r'.ogg'): newName = newName[:-4] + r'.ogv'
            elif (newName[-4:] == r'.asf'): newName = newName[:-4] + r'.wmv'
            elif (newName[-5:] == r'.riff'): newName = newName[:-4] + r'.avi'
        else:
            newName = songFilename(currentPath, parsedInfo)
            if (newName[-4:] == r'.mp4'): newName = newName[:-4] + r'.m4a'
            elif (newName[-4:] == r'.asf'): newName = newName[:-4] + r'.wma'
            elif (newName[-5:] == r'.riff'): newName = newName[:-5] + r'.wav'
            elif (newName[-3:] == r'.rm'): newName = newName[:-4] + r'.ra'
            elif (newName[-5:] == r'.rmvb'): newName = newName[:-5] + r'.ra'
        return newName
    except:
        return os.path.split(currentPath)[-1]

def PDFFilename( currentPath ):
    try:
        document = PDFFile(currentPath, strict=False)
        if (document.isEncrypted): return os.path.split(currentPath)[-1]
        info = document.documentInfo
        if (info is None): return os.path.split(currentPath)[-1]
        author = info.get(r'/Author', r'')
        if (isinstance(author, PDFIndirectObject)): author = document.getObject(author)
        author = (author + r' - ') if (author is not None) else r''
        title = info.get(r'/Title', r'')
        if (isinstance(title, PDFIndirectObject)): title = document.getObject(title)
        if (not title): return os.path.split(currentPath)[-1]
        return (normalizedFilename(author + title) + r'.pdf')
    except:
        return os.path.split(currentPath)[-1]

def OLEDocumentFilename( currentPath ):
    try:
        document = OLEFile(currentPath)
        documentMetadata = document.get_metadata()
        document.close()
        encoding = documentMetadata.codepage
    except:
        return os.path.split(currentPath)[-1]
    encoding = encodingName(r'cp' + str(encoding if (encoding) else 1252))
    author = r''
    if ((documentMetadata.author is not None) and (len(documentMetadata.author) > 1)):
        author = r' (' + documentMetadata.author.decode(encoding, r'ignore') + r')'
    if ((documentMetadata.title is not None) and (len(documentMetadata.title) > 1)):
        title = normalizedFilename(documentMetadata.title.decode(encoding, r'ignore'))
        return (normalizedFilename(title + author) + os.path.splitext(currentPath)[-1])
    return os.path.split(currentPath)[-1]

def openXMLDocumentFilename( currentPath ):
    try:
        document = ZIPFile(currentPath, r'r')
        XMLMetadataFile = document.open(r'docProps/core.xml')
        parsedXML = parsedXML(XMLMetadataFile)
        if (parsedXML is None): return os.path.split(currentPath)[-1]
        field = parsedXML.find('//creator')
        author = (r' (' + field.text + r')') if (field is not None) else r''
        field = parsedXML.find('//title')
        if ((field is not None) and (len(field.text) > 1)): title = field.text
        else: return os.path.split(currentPath)[-1]
        XMLMetadataFile.close()
        return (normalizedFilename(title + author) + os.path.splitext(currentPath)[-1])
    except:
        return os.path.split(currentPath)[-1]

def openDocumentFilename( currentPath ):
    try:
        with open(currentPath, r'rb') as document:
            fileSignature = document.read(2)
            document.seek(0)
            if (fileSignature == b'<?'): parsedXML = parsedXML(document)
            else: fileSignature = None
        if (fileSignature is None):
            XMLMetadataFile = ZIPFile(currentPath, r'r').open(r'meta.xml')
            parsedXML = parsedXML(XMLMetadataFile)
        if (parsedXML is None): return os.path.split(currentPath)[-1]
        field = parsedXML.find(r'//initial-creator')
        if (field is None): field = parsedXML.find(r'//creator')
        author = (r' (' + field.text + r')') if (field is not None) else r''
        field = parsedXML.find(r'//title')
        if ((field is not None) and (len(field.text) > 1)): title = field.text
        else: return os.path.split(currentPath)[-1]
        return (normalizedFilename(title + author) + os.path.splitext(currentPath)[-1])
    except:
        return os.path.split(currentPath)[-1]

def HTMLFilename( currentPath, xml=None ):
    try:
        if (xml is None): xml = html.parse(currentPath)
        title = xml.find(r'.//title')
        if (title is None):
            title = xml.find(r'.//meta[@name="title"]')
            if (title is None): title = xml.find(r'.//meta[@property="og:title"]')
            if (title is None): title = xml.find(r'.//meta[@name="parsely-title"]')
            if (title is None): title = xml.find(r'.//name')
    except:
        title = None
    if (title is None): return os.path.split(currentPath)[-1]
    else: return (normalizedFilename(title.text) + os.path.splitext(currentPath)[-1])

def HTMLGZFilename( currentPath ):
    try: xml = html.fromstring(gzip.open(currentPath, r'rb').read())
    except: return os.path.split(currentPath)[-1]
    return (HTMLFilename(currentPath[:-3], xml) + r'.gz')

def EPUBFilename( currentPath ):
    try:
        content = ZIPFile(currentPath, r'r')
        for component in sorted(content.namelist(), key=len):
            if (component.endswith(r'.opf')):
                parsedXML = parsedXML(content.open(component))
                break
    except:
        parsedXML = None
    if (parsedXML is not None):
        title = parsedXML.find('//title')
        if ((title is not None) and len(title.text)):
            field = parsedXML.find('//creator')
            author = r'' if ((field is None) or (not field.text)) else (field.text + r' - ')
            field = parsedXML.find('//publisher')
            publisher = r'' if ((field is None) or (not field.text)) else (r' (' + field.text + ')')
            return (normalizedFilename(author + title.text + publisher) + r'.epub')
    return os.path.split(currentPath)[-1]

def fontFilename( currentPath ):
    try: font = ttLib.TTFont(currentPath)
    except: return os.path.split(currentPath)[-1]
    name = r''
    family = r''
    _mute()
    try:
        for record in font[r'name'].names:
            if (b'\x00' in record.string):
                name_str = record.string.decode(r'utf-16-be', r'ignore')
            else:
                try: name_str = record.string.decode(r'utf-8')
                except: name_str = record.string.decode(r'latin-1', r'ignore')
            if ((record.nameID == 2) and (not name)): name = name_str
            elif ((record.nameID == 1) and (not family)): family = name_str
            if (name and family): break
    except:
        _unmute()
        return os.path.split(currentPath)[-1]
    path = currentPath.rsplit(os.path.sep, 1)[0]
    name = normalizedFilename(family + r' ' + name)
    _unmute()
    if (len(name) < 2): return os.path.split(currentPath)[-1]
    return (name + r'.' + currentPath.rsplit(r'.', 1)[-1])

def torrentFilename( currentPath ):
    if (not os.path.isfile(currentPath)): return os.path.split(currentPath)[-1]
    with open(currentPath, r'rb') as f:
        try: content = f.readline()
        except: return os.path.split(currentPath)[-1]
        content = content.split(b'6:pieces')[0]
        try:
            encoding = cchardet.detect(content)[r'encoding']
            encoding = codecs.lookup(encoding if (encoding is not None) else r'utf-8').name
        except:
            encoding = r'utf-8'
        content = content.decode(encoding, r'ignore')
        name = re.findall(r'4:name([0-9]+):', content)
        if (not name): return os.path.split(currentPath)[-1]
        name = re.findall(r'4:name' + name[0] + ':(.{' + name[0] + '})', content)
        if (not name): return os.path.split(currentPath)[-1]
        path = currentPath.rsplit(os.path.sep, 1)[0]
        return (normalizedFilename(name[0]) + r'.torrent')

windowsPlaylistTitle = re.compile(r'<title>(.*)</title>')
def windowsPlaylistFilename( currentPath ):
    title = None
    try:
        with open(currentPath, r'rb') as f:
            title = windowsPlaylistTitle.findall(decodedFileContent(f))
            if ((len(title) > 0) and (len(title[0]) > 0)):
                title = windowsPlaylistTitle.sub(r'\1', title[0])
    except:
        pass
    if (not title): return os.path.split(currentPath)[-1]
    else: return (normalizedFilename(title) + r'.wpl')

def cueSheetFilename( currentPath ):
    title = None
    try:
        with open(currentPath, r'rb') as f:
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
    if (not title): return os.path.split(currentPath)[-1]
    else: return (normalizedFilename(title) + r'.cue')

desktopEntryNameLine1 = re.compile(r'\nExec=([^\n\t ]+)')
desktopEntryNameLine2 = re.compile(r'\nName=([^\n#]*)')
def desktopEntryFilename( currentPath ):
    newFilename = r''
    try:
        with open(currentPath, r'rb') as f:
            content = decodedFileContent(f)
            newFilename = desktopEntryNameLine1.findall(content)
            if (len(newFilename) < 1):
                newFilename = desktopEntryNameLine2.findall(content)
                if (len(newFilename)):
                    newFilename = re.sub(r'\s+', r'-', newFilename[0].lower())
            else:
                newFilename = os.path.splitext(os.path.split(newFilename[0])[-1])[0]
            if (not newFilename): return os.path.split(currentPath)[-1]
            else: return normalizedFilename(newFilename + '.desktop')
    except:
        return os.path.split(currentPath)[-1]

windowsRegistryFile = re.compile(r'.*\.(dat|hve|man|reg)(\.tmp)?$', re.IGNORECASE)
def windowsRegistryFilename( currentPath ):
    try:
        regName = b'\x00' * 64
        REGEDIT4 = False
        with open(currentPath, r'rb') as reg:
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
        if (len(regName) < 1): return os.path.split(currentPath)[-1]
        if (not windowsRegistryFile.match(regName)): regName += r'.reg'
        return normalizedFilename(re.sub(r'^([A-Z]):\\', r'\1_', regName).replace('\\', r'_'))
    except:
        return os.path.split(currentPath)[-1]



# VISUAL IMAGE DEDUPLICATION FUNCTIONS

def averageRGB( image ):
    if (not image.mode.startswith(r'RGB')):
        image.convert(r'RGB' if (image.mode[-1] != r'A') else r'RGBA')
    data = list(image.getdata())
    if (not (isinstance(data[0], tuple) and (len(data[0]) == 3))): return None
    avgR, avgG, avgB = 0, 0, 0
    for RGB in data:
        avgR += RGB[0]
        avgG += RGB[1]
        avgB += RGB[2]
    return (round(avgR / len(data)), round(avgG / len(data)), round(avgB / len(data)))

def similarEnoughRGBColors( RGB1, RGB2 ):
    if ((RGB1 is None) or (RGB2 is None)): return True
    RGB = (abs(RGB1[0] - RGB2[0]), abs(RGB1[1] - RGB2[1]), abs(RGB1[2] - RGB2[2]) >= 10)
    if ((RGB[0] > 10) or (RGB[1] > 10) or (RGB[2] > 10) or ((RGB[0] + RGB[1] + RGB[2]) > 15)):
        return False
    return True

def imageWithInfo( imagePath ):
    try: image = Image.open(imagePath, r'r').convert(r'RGB')
    except: return (0, (-999, -999), (999, 999, 999), None)
    if (image.size[0] >= image.size[1]):
        return (int((image.size[0] / image.size[1]) * 1000), image.size, None, imagePath)
    else:
        return (int((image.size[1] / image.size[0]) * (-1000)), image.size, None, imagePath)

def sameRatio( A, B ):
    Aw, Ah = A
    Bw, Bh = B
    if (abs(Ah - Aw) < (((Ah + Aw) / 2) * 0.01)):
        if (abs(Bh - Bw) > (((Bh + Bw) / 2) * 0.01)): return False
        ratioA = 1
        ratioB = round((max([Bh, Bw]) / min([Bh, Bw])), 2)
    elif (Aw > Ah):
        if (not (Bw > Bh)): return False
        ratioA = round((Aw / Ah), 2)
        ratioB = round((Bw / Bh), 2)
    else:
        if (not (Bh > Bw)): return False
        ratioA = round((Ah / Aw), 2)
        ratioB = round((Bh / Bw), 2)
    return (round(abs(ratioA - ratioB), 2) <= 0.01)

def similarEnoughImages( imageA, imageB, resizing ):
    A = list(imageA.getdata())
    B = list(imageB.getdata())
    if (not (isinstance(A[0], tuple) and isinstance(B[0], tuple) and
             (len(A[0]) == 3) and (len(B[0]) == 3))):
        return False
    diff = []
    for i in range(len(A)):
        diff += [abs(A[i][0] - B[i][0]), abs(A[i][1] - B[i][1]), abs(A[i][2] - B[i][2])]
    return ((sum(diff) / len(diff)) < (5 + (min(resizing, 10) // 2)))

def similarEnoughImagesWithAlpha( imageA, imageB, resizing ):
    A = list(imageA.getdata())
    B = list(imageB.getdata())
    if (not (isinstance(A[0], tuple) and isinstance(B[0], tuple) and
             (len(A[0]) == 4) and (len(B[0]) == 4))):
        return False
    diff = []
    for i in range(len(A)):
        diff += [abs(A[i][0] - B[i][0]), abs(A[i][1] - B[i][1]),
                 abs(A[i][2] - B[i][2]), abs(A[i][3] - B[i][3])]
    return ((sum(diff) / len(diff)) < (5 + (min(resizing, 10) // 2)))

def sameImages( imageA, imageB ):
    sizeA = imageA.size[0] + imageA.size[1]
    sizeB = imageB.size[0] + imageB.size[1]
    if (imageA.size > imageB.size): imageA = imageA.resize(imageB.size)
    elif (imageA.size < imageB.size): imageB = imageB.resize(imageA.size)
    if ((imageA.mode[-1] == r'A') or (imageB.mode[-1] == r'A')):
        if (imageA.mode != r'RGBA'): imageA.convert(r'RGBA')
        if (imageB.mode != r'RGBA'): imageB.convert(r'RGBA')
        return similarEnoughImagesWithAlpha(imageA, imageB, (max(sizeA, sizeB) / min(sizeA, sizeB)))
    else:
        if (imageA.mode != r'RGB'): imageA.convert(r'RGB')
        if (imageB.mode != r'RGB'): imageB.convert(r'RGB')
        return similarEnoughImages(imageA, imageB, (max(sizeA, sizeB) / min(sizeA, sizeB)))

def removeSmallerVisualDuplicates( duplicatesGroup ):
    deduped = 0
    if (len(duplicatesGroup) > 1):
        duplicatesGroup = sorted(duplicatesGroup)
        largestSize = duplicatesGroup[-1][0]
        largest = [image for size, image in duplicatesGroup if (size >= largestSize)]
        if (len(largest) == 1): largest = largest[0]
        else: largest = max(largest, key=lambda f: fileSize(f))
        for size, image in duplicatesGroup:
            if ((image != largest) and os.path.exists(image)):
                removeFile(image)
                deduped += 1
    return deduped



# FILES PROCESSING LOOP FUNCTIONS

def junkRemovalLoop( files, target, junkDetectionFunction ):
    global done
    buffer = []
    if (isinstance(target, str)):
        def isTarget( filePath ): return filePath.endswith(target)
    elif (isinstance(target, re.Pattern)):
        def isTarget( filePath ): return target.match(filePath)
    else:
        return
    for i in range(len(files)):
        if (isTarget(files[i]) and junkDetectionFunction(files[i])):
            done += 1
            progress(r'Analyzing files...', done, initialTotal)
            removeJunkFile(files[i])
        else:
            buffer.append(files[i])
    return buffer

def renamingLoop( files, target, filenameFunction ):
    global done
    buffer = []
    if (isinstance(target, str)):
        def isTarget( filePath ): return filePath.endswith(target)
    elif (isinstance(target, re.Pattern)):
        def isTarget( filePath ): return target.match(filePath)
    else:
        return
    for i in range(len(files)):
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
pictureFile += r'j(p[2efx]|[np]g|peg|xr)|m(ic|po|sp|ng)|p(c[dx]|ng|[abgnp]m|s[db])|odg|c(in|r2|rw|ur|dr)|'
pictureFile = re.compile(pictureFile + r'[hw]dp|heic|s(gi|vgz?)|t(ga|iff?)|w(al|ebp|mf|bmp|pg)|x([bp]m|cf))$')
ambigMediaFile = re.compile(r'^.*\.(asf|ogg|webm|rm|riff|3g(p?[p2]|pp2))$')
videoFile = re.compile('^.*\.(avi|(fl|mq|vi|wm)v|m([4ko]v|p(4|e|e?g))|ogv|qt|rmvb)$')
documentFile = r'^.*\.((f?od|uo)[pst]|o(le|pf)|(xls|ppt|doc)x?|p(df|s|ps)|g(p[345x]?|tp)|tg|css|'
documentFile = re.compile(documentFile + r'e(nc|pub)|[a-z]?html?(\.gz)?|m(obi|d)|djvu?|chm|rtf|[tc]sv|dcx)$')
audioFile = r'^.*\.(m(4[abp]|ka|p[+c123]|idi?)|w(ma|a?v)|flac|a(ac|c3|pe|u)|dts|oga|tta|gsm|'
audioFile = re.compile(audioFile + r'ra|ofr|s(px|nd))$')

metadatalessFile = re.compile(r'^.*\.(json|class|m3u|log|pyc)$')

photorecName = re.compile(r'^(.*/)?[ft][0-9]{5,}(_[^/]*)?(\.[a-zA-Z0-9]+)?$')



# SILENCING WARNINGS FOR THEY (THE ONES EXPECTED) ARE NOT RELEVANT

warnings.simplefilter(r'ignore')



# PROCESSING COMMAND LINE ARGUMENTS

if ((r'-h' in sys.argv) or (r'--help' in sys.argv)): helpMessage()

option_runningWithSudo = not os.getuid()

targetRootDir = None
photoRecTarget = None
commaSeparatedExtensions = re.compile(r'[a-zA-Z0-9][a-zA-Z0-9.+-]*(,[a-zA-Z0-9][a-zA-Z0-9.+-]*)*')
number = re.compile(r'0*[1-9][0-9]*')
junkExtensions = r''
maxFilesPerDir = 250
waitingPhotoRecArg = False
waitingRBFList = False
waitingMaxFilesPerDir = False
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
    elif (arg == r'-m'):
        waitingMaxFilesPerDir = True
    elif (waitingRBFList):
        waitingRBFList = False
        if (commaSeparatedExtensions.match(arg)): junkExtensions += arg
        else: error("Invalid file extensions list: '" + arg + "'", 2)
    elif (waitingMaxFilesPerDir):
        waitingMaxFilesPerDir = False
        if (number.match(arg)): maxFilesPerDir = int(arg)
        else: error("Invalid value: '" + arg + "'", 2)

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
        print('\n', end=r'', flush=True)
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

option_removeDuplicates = r'-D' not in sys.argv
option_dedupAcrossExtensions = r'-d' in sys.argv
option_visuallyDedupImages = r'-I' in sys.argv
option_keepDirStructure = (r'-k' in sys.argv) or (r'-K' in sys.argv)
option_wipeEmptyDirs = r'-K' not in sys.argv
option_skipRenaming = r'-N' in sys.argv
option_photorecNamesOnly = r'-n' in sys.argv
option_DeepDedupTxts = r'-T' in sys.argv
option_keepEmptyFiles = r'-z' in sys.argv
option_skipAnalysis = option_skipRenaming and (not option_removeKnownJunk)



# GENERATING THE LIST OF FILES TO BE PROCESSED

print(r'Listing files...', end=r'', flush=True)
ellapsedTime = time.monotonic()
files = []
try:
    for path, subdirs, items in os.walk(targetRootDir):
        files += [os.path.join(path, name) for name in items]
        progress(r'Listing files...', len(files), 0)
except PermissionError as e:
    error(("\rCannot access '" + e.filename + "' (try running as root)"), 1)
initialTotal = len(files)
if (not initialTotal):
    _clearLine()
    print('Empty directory', flush=True)
    exit(0)
if (not option_runningWithSudo):
    for i in range(initialTotal):
        progress('Checking files\x27 permissions...', i, initialTotal)
        if (not os.access(files[i], os.R_OK)):
            error(("\rCannot access '" + files[i] + "' (try running as root)"), 1)
if (option_dedupAcrossExtensions):
    files = [(fileSize(file), None, file) for file in files]
else:
    files = [(fileSize(file), os.path.splitext(file)[-1], file) for file in files]
if (option_photorecNamesOnly):
    files = [(size, ext, file) for size, ext, file in files if photorecName.match(file)]
files = sorted(files)
ellapsedTime = time.monotonic() - ellapsedTime
stepConclusion(r'# file_ found', initialTotal, ellapsedTime)



# REMOVING EMPTY FILES

if (not option_keepEmptyFiles):
    print(r'Removing empty files...', end=r'', flush=True)
    j = 0
    ellapsedTime = time.monotonic()
    if (files[0][0] == 0):
        for i in range(len(files)):
            if (files[i][0] != 0): break
            j += 1
        for i in range(0, j):
            progress(r'Removing empty files...', (j - (j - i)), j)
            try: removeFile(files[i][2])
            except FileNotFoundError: pass
        files = files[j:]
        initialTotal -= j
    ellapsedTime = time.monotonic() - ellapsedTime
    stepConclusion(r'# empty file_ removed', j, ellapsedTime)



# DEDUPLICATING FILES

if (option_removeDuplicates):
    print(r'Deduplicating files...', end=r'', flush=True)
    ellapsedTime = time.monotonic()
    done = 0
    actuallyDeduped = 0
    from struct import unpack
    signatures, tails = [0] * len(files), [0] * len(files)
    for i in range(len(files)):
        try:
            with open(files[i], r'rb') as f:
                signatures[i] = unpack(r'i', f.read(4))[0]
                f.seek(-4, 2)
                tails[i] = unpack(r'i', f.read(4))[0]
        except:
            signatures[i], tails[i] = None, None
        progress(r'Preanalysing found files for deduplication...', i, initialTotal)
    _clearLine()
    for i in range(len(files)):
        if (files[i][0] == -1): continue
        for j in range((i + 1), len(files)):
            if (files[j][0] == -1): continue
            elif (files[i][0] != files[j][0]): break
            elif ((signatures[i] != signatures[j]) or (tails[i] != tails[j])): continue
            elif (files[i][1] == files[j][1]):
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
                    removeFile(files[j][2])
                    files[j] = (-1, r'/', files[j][2])
        done += 1
        progress(r'Deduplicating files...', (actuallyDeduped + done), initialTotal)
    del signatures, tails
    initialTotal -= actuallyDeduped
    ellapsedTime = time.monotonic() - ellapsedTime
    stepConclusion(r'# duplicate_ removed', actuallyDeduped, ellapsedTime)



# STARTING TO PROCESS FILES

if (not option_skipAnalysis):
    if (option_photorecNamesOnly):
        files = sorted([file for size, ext, file in files if ((size > 0) and photorecName.match(file))])
    else:
        files = sorted([file for size, ext, file in files if (size > 0)])
    print(r'Analyzing files...', end=r'', flush=True)
    done = 0
    ellapsedTimeRenaming, ellapsedTimeRemovingJunk = 0, 0



# REMOVING JUNK FILES

if (option_removeKnownJunk):
    ellapsedTime = time.monotonic()
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

    files = junkRemovalLoop(files, r'.gz', isBadGZ)
    files = junkRemovalLoop(files, r'.zip', isBadZIP)
    files = junkRemovalLoop(files, pictureFile, isBadImage)

    ellapsedTimeRemovingJunk = time.monotonic() - ellapsedTime



# REMOVING UNSUPPORTED FILES FROM THE LIST

if (not option_skipAnalysis):
    files = [file for file in files if (not metadatalessFile.match(file))]
    done = initialTotal - len(files)
    progress(r'Analyzing files...', done, initialTotal)



# PROCESSING PLAIN TEXT FILES

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
for i in range(len(files)):
    if (files[i].endswith(r'.txt') and os.path.isfile(files[i])):
        with open(files[i], r'rb') as f:
            content = decodedFileContent(f)
            lineCount = content.count('\n')
            if (content.startswith(r'<?xml')):
                buffer.append(changeExtension(files[i], 3, r'xml', count=True))
            elif (len(srtTime.findall(content)) > max(1, (lineCount / 8))):
                buffer.append(changeExtension(files[i], 3, r'srt', count=True))
            elif ((r'<!-- Created with Inkscape (http://www.inkscape.org/) -->' in content) and
                (r'</svg>' in content)):
                buffer.append(changeExtension(files[i], 3, r'svg', count=True))
            elif (len(tclLine.findall(content)) > 0):
                buffer.append(changeExtension(files[i], 3, r'tcl', count=True))
            else:
                if ((lineCount > 6) and
                    ((len(logLine1.findall(content)) >= (lineCount - 1)) or
                    (len(logLine2.findall(content)) >= (lineCount - 1)) or
                    (len(logLine3.findall(content)) >= (lineCount - 1)))):
                    changeExtension(files[i], 3, r'log', count=True)
                elif (maybeJSON.match(content)):
                    try:
                        junk = json.loads(content)
                        rename(files[i], (os.path.split(files[i])[-1][:-4] + r'.json'))
                        del junk
                        continue
                    except:
                        pass
                gpd_pcfName = gpd_pcfNameLine.findall(content)
                if (len(gpd_pcfName) == 1):
                    newFilename = normalizedFilename(gpd_pcfName[0][1])
                    newFilename = re.sub(r'(\.[GgPp][Pp][Dd])$', lambda x: x.group(0).lower(), newFilename)
                    rename(files[i], newFilename)
                    continue
                elif (((lineCount > 6) and (len(xmlLine.findall(content)) >= (lineCount - 1)) and
                      (len(windowsJunkXMLLine.findall(content)) > (lineCount / 6))) or
                      (len(set(content)) < min(12, round(len(content) / 2))) or
                      (content.startswith(r'# Autogenerated by Sphinx'))):
                    removeJunkFile(files[i])
                done += 1
        progress(r'Analyzing files...', done, initialTotal)
    else:
        buffer.append(files[i])
files = buffer

ssaLine = re.compile(r'(^|\n)Dialogue: [0-9]+,[0-9]+:([0-5][0-9]|60):([0-5][0-9]|60)\.[0-9]{2}')
buffer = []
for i in range(len(files)):
    if (files[i].endswith(r'.ini') and os.path.isfile(files[i])):
        with open(files[i], r'rb') as f:
            content = decodedFileContent(f)
            lineCount = content.count('\n')
            if (content.startswith(r'[Script Info]')):
                if (len(ssaLine.findall(content)) > max(1, ((lineCount / 3) - 25))):
                    buffer.append(changeExtension(files[i], 3, r'ass', count=True))
                else:
                    buffer.append(files[i])
            elif (content.startswith(r'[Desktop Entry]')):
                buffer.append(changeExtension(files[i], 3, r'desktop', count=True))
            else:
                if (content.startswith(r'[General]\s*\n\s*Version=DrumSynth v2\.0')):
                    changeExtension(files[i], 3, r'ds', count=True)
                elif (content.startswith((r'[MIME Cache]', r'[.ShellClassInfo]'))):
                    removeJunkFile(files[i])
                elif (content.startswith(r'[Device Install Log]')):
                    changeExtension(files[i], 3, r'log', count=True)
                done += 1
        progress(r'Analyzing files...', done, initialTotal)
    else:
        buffer.append(files[i])
files = buffer



# PROCESSING CODE FILES

variableName = r'^[a-zA-Z_][a-zA-Z0-9_]*'
cppLine = r'((^|\n)[\t ]*(namespace\s*' + variableName + '\s*\{|class\s*' + variableName
cppLine += r'\s*[;:{]|#include <[^<>]*([^.][^h]|\.hpp)>|cout\s*<<|cin\s*>>|template\s*<[^\n;]*>)|'
cppLine = re.compile(cppLine + '::|\x22\x22_' + variableName + r')')
cComments = re.compile(r'(//.*?\n|/\*.*?\*/)')
cStrings = re.compile('(\x22.*?[^\\\\]\x22|\x27.*?[^\\\\]\x27)')
buffer = []
for i in range(len(files)):
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
    else:
        buffer.append(files[i])
files = buffer



# SMARTLY RENAMING FILES

if (not option_skipRenaming):
    # Improving Some Filenames Photorec Sometimes Provides
    prenamedFile1 = r'^[ft][0-9]{5,}_([^_].*)[._](([dr]ll|exe|sys|ocx|cpl|tsp)(_mui)?|'
    prenamedFile1 = re.compile(prenamedFile1 + r'winmdobj|bin|d2s)$', re.IGNORECASE)
    prenamedFile2 = r'^[ft][0-9]{5,}_([^_].*)[._](zip|pdf|doc|xls|'
    prenamedFile2 = re.compile(prenamedFile2 + r'pp[st])$', re.IGNORECASE)
    prenamedFileGeneric = re.compile(r'^[ft][0-9]{5,}_([^_].*)$')
    def fixedPhotoRecName1( match ):
        return (match.group(1) + r'.' + match.group(2).lower().replace(r'_', r'.'))
    def fixedPhotoRecName2( match ):
        return (re.sub(r'\s+', r' ', match.group(1).replace(r'_', r' ')).strip() + r'.' +
                match.group(2).lower().replace(r'_', r'.'))
    ellapsedTime = time.monotonic()
    buffer = []
    for i in range(len(files)):
        filename = files[i].rsplit(os.path.sep, 1)[-1]
        if (prenamedFile1.match(filename)):
            done += 1
            progress(r'Analyzing files...', done, initialTotal)
            rename(files[i], prenamedFile1.sub(fixedPhotoRecName1, filename), count=True)
        elif (prenamedFile2.match(filename)):
            done += 1
            progress(r'Analyzing files...', done, initialTotal)
            rename(files[i], prenamedFile2.sub(fixedPhotoRecName2, filename), count=True)
        elif (filename.endswith(r'.pf')):
            rename(files[i], prenamedFileGeneric.sub(r'\1', filename), count=True)
        else:
            buffer.append(files[i])
    unsupported = re.compile(r'^.*\.(d2s|bin|([dr]ll|exe|sys|ocx|cpl|tsp)(\.mui)?)$')
    files = [file for file in buffer if (not unsupported.match(file))]
    done = initialTotal - len(files)
    progress(r'Analyzing files...', done, initialTotal)

    files = renamingLoop(files, r'.java', javaCSharpFilename)
    files = renamingLoop(files, r'.cs', javaCSharpFilename)

    files = renamingLoop(files, pictureFile, imageFilename)

    files = renamingLoop(files, r'.mp4', ambigMediaFilename)
    files = renamingLoop(files, ambigMediaFile, ambigMediaFilename)
    files = renamingLoop(files, audioFile, songFilename)
    files = renamingLoop(files, videoFile, videoFilename)

    files = renamingLoop(files, r'.pdf', PDFFilename)
    files = renamingLoop(files, re.compile(r'^.+\.(doc|xls|ppt|ole)$'), OLEDocumentFilename)
    files = renamingLoop(files, re.compile(r'^.+\.(doc|xls|ppt)x$'), openXMLDocumentFilename)
    files = renamingLoop(files, re.compile(r'^.+\.f?od[gpst]$'), openDocumentFilename)
    files = renamingLoop(files, re.compile(r'^.+\.[a-z]?html?$'), HTMLFilename)
    files = renamingLoop(files, re.compile(r'^.+\.[a-z]?html?\.gz$'), HTMLGZFilename)
    files = renamingLoop(files, r'.epub', EPUBFilename)

    files = renamingLoop(files, fontFile, fontFilename)

    files = renamingLoop(files, r'.torrent', torrentFilename)

    files = renamingLoop(files, r'.wpl', windowsPlaylistFilename)
    files = renamingLoop(files, r'.cue', cueSheetFilename)

    files = renamingLoop(files, r'.desktop', desktopEntryFilename)
    files = renamingLoop(files, r'.reg', windowsRegistryFilename)
    ellapsedTimeRenaming = time.monotonic() - ellapsedTime



# SOME VERBOSITY

if (not option_skipAnalysis):
    stepConclusion(r'# file_ analyzed', done, (ellapsedTimeRenaming + ellapsedTimeRemovingJunk))
if (not option_skipRenaming):
    stepConclusion(r'# file_ renamed', renamedFiles, ellapsedTimeRenaming)
if (option_removeKnownJunk):
    stepConclusion(r'# junk file_ removed', removedJunkFiles, ellapsedTimeRemovingJunk)



# REMOVING FILES BY EXTENSION (IF SPECIFIED)

if (len(junkExtensions) > 0):
    print(r'Removing files by extension...', end=r'', flush=True)
    ellapsedTime = time.monotonic()
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
    ellapsedTime = time.monotonic() - ellapsedTime
    stepConclusion(r'# file_ removed by extension', done, ellapsedTime)



# DEDUPLICATING PLAIN TEXTS BASED ON CONTENT (IF SPECIFIED)

if (option_DeepDedupTxts):
    print(r'Deduplicating plain texts...', end=r'', flush=True)
    ellapsedTime = time.monotonic()
    done = 0
    actuallyDeduped = 0
    files = []
    for path, subdirs, items in os.walk(targetRootDir):
        files += [os.path.join(path, name) for name in items if name.endswith(r'.txt')]
    initialTotal = len(files)
    i = SharedValue(r'i', 0)
    whitespace = re.compile(r'\s+', re.MULTILINE)
    def preprocessedTextWithProgress( imageFile ):
        with i.get_lock(): i.value += 1
        progress(r'Preanalysing found plain texts...', i.value, initialTotal)
        try:
            with open(imageFile, r'rb') as f:
                content = unormalize(r'NFC', decodedFileContent(f).translate(_table))
                return whitespace.sub(r'', content.casefold())
        except:
            return r''
    with Pool(len(os.sched_getaffinity(0))) as p:
        contents = p.map(preprocessedTextWithProgress, files)
    for i in range(len(files)): files[i] = (len(contents[i]), files[i])
    files = sorted(files, reverse=True)
    for i in range(len(files)):
        if ((not files[i][-1]) or (not files[i][0]) or (not contents[i])): continue
        done += 1
        progress(r'Deduplicating plain texts...', done, initialTotal)
        for j in range((i + 1), len(files)):
            if ((not files[j][-1]) or (not files[j][0]) or (not contents[j])): continue
            if (files[i][0] != files[j][0]): break
            if (contents[i][0] != contents[j][0]): continue
            if (contents[i][-1] != contents[j][-1]): continue
            if (contents[i] == contents[j]):
                try:
                    removeFile(files[j][-1])
                    files[j] = (0, None)
                    done += 1
                    actuallyDeduped += 1
                    progress(r'Deduplicating plain texts...', done, initialTotal)
                except:
                    pass
    ellapsedTime = time.monotonic() - ellapsedTime
    stepConclusion(r'# duplicate plain text_ removed', actuallyDeduped, ellapsedTime)



# DEDUPLICATING IMAGES VISUALLY (IF SPECIFIED)

if (option_visuallyDedupImages):
    deduplicablePictureFile = r'^.*\.(b([lm]p|pg)|d(c[rx]|ds|ib)|emf|g(d|if)|i(mt?|co|cns)|flif|'
    deduplicablePictureFile += r'j(p[2efx]|[np]g|peg|xr)|m(ic|po|sp|ng)|p(c[dx]|ng|[abgnp]m)|'
    deduplicablePictureFile += r'c(in|r2|rw)|[hw]dp|heic|sgi|tga|w(al|ebp|mf|bmp|pg)|'
    deduplicablePictureFile = re.compile(deduplicablePictureFile + r'x[bp]m)$')
    print(r'Visually deduplicating images...', end=r'', flush=True)
    ellapsedTime = time.monotonic()
    done = 0
    actuallyDeduped = 0
    files = []
    for path, subdirs, items in os.walk(targetRootDir):
        files += [os.path.join(path, name) for name in items if deduplicablePictureFile.match(name)]
    initialTotal = len(files)
    i = SharedValue(r'i', 0)
    def imageWithInfoAndProgress( imageFile ):
        with i.get_lock(): i.value += 1
        progress(r'Preanalysing found images...', i.value, initialTotal)
        return imageWithInfo(imageFile)
    with Pool(len(os.sched_getaffinity(0))) as p:
        files = p.map(imageWithInfoAndProgress, files)
        files = sorted(sorted(files, key=lambda f: (f[1][0] + f[1][1]), reverse=True))
    for i in range(len(files)):
        if (not files[i][-1]): continue
        done += 1
        image = None
        progress(r'Visually deduplicating images...', done, initialTotal)
        currentGroup = [((files[i][1][0] + files[i][1][1]), files[i][-1])]
        for j in range((i + 1), len(files)):
            if (not files[j][-1]): continue
            if (not sameRatio(files[i][1], files[j][1])): break
            if (not similarEnoughRGBColors(files[i][2], files[j][2])): continue
            if (image is None):
                try: image = Image.open(files[i][-1])
                except: break
                if (files[i][2] is None):
                    files[i] = (files[i][0], files[i][1], averageRGB(image), files[i][-1])
            try:
                anotherImage = Image.open(files[j][-1])
            except:
                files[j] = (0, files[j][1], files[j][2], None)
                continue
            if (files[j][2] is None):
                files[j] = (files[j][0], files[j][1], averageRGB(anotherImage), files[j][-1])
            if (sameImages(image, anotherImage)):
                currentGroup.append(((files[j][1][0] + files[j][1][1]), files[j][-1]))
                files[j] = (0, files[j][1], files[j][2], None)
                done += 1
                progress(r'Visually deduplicating images...', done, initialTotal)
        actuallyDeduped += removeSmallerVisualDuplicates(currentGroup)

    ellapsedTime = time.monotonic() - ellapsedTime
    stepConclusion(r'# duplicate image_ removed', actuallyDeduped, ellapsedTime)



# SORTING FILES INTO MORE MEANINGFUL SUBDIRECTORIES

if (not option_keepDirStructure):
    print(r'Organizing files...', end=r'', flush=True)
    ellapsedTime = time.monotonic()
    done = 0
    files = []
    for path, subdirs, items in os.walk(targetRootDir):
        files += [os.path.join(path, name) for name in items]
    initialTotal = len(files)
    audioDir, docsDir, fontsDir, picsDirs, videosDir, txtDir, codeDir, miscDir = createSubdirs(
        targetRootDir,
        [r'Audio',  r'Documents',  r'Fonts', r'Pictures',
         r'Videos', r'Plain Text', r'Code',  r'Misc'])
    for file in files:
        if (ambigMediaFile.match(file)):
            try:
                video = bool(len(MediaInfo.parse(file).video_tracks))
                files[done] = moveNotReplacing(file, (videosDir if video else audioDir))
            except:
                files[done] = moveNotReplacing(file, miscDir)
        elif (file.endswith(r'.djvu')):
            try:
                with open(file, r'rb') as djvu:
                    content = djvu.read(32).decode(r'cp1252', r'ignore')
                document = bool(re.match(r'^AT&TFORM([^\x21-\x7E]*)DJVM', content))
                files[done] = moveNotReplacing(file, (docsDir if document else picsDirs))
            except:
                files[done] = moveNotReplacing(file, docsDir)
        else:
            if (file.endswith(r'.txt')): files[done] = moveNotReplacing(file, txtDir)
            elif (fontFile.match(file)): files[done] = moveNotReplacing(file, fontsDir)
            elif (videoFile.match(file)): files[done] = moveNotReplacing(file, videosDir)
            elif (audioFile.match(file)): files[done] = moveNotReplacing(file, audioDir)
            elif (documentFile.match(file)): files[done] = moveNotReplacing(file, docsDir)
            elif (pictureFile.match(file)): files[done] = moveNotReplacing(file, picsDirs)
            elif (codeFile.match(file)): files[done] = moveNotReplacing(file, codeDir)
            else: files[done] = moveNotReplacing(file, miscDir)
        done += 1
        progress(r'Organizing files...', done, initialTotal)

    ellapsedTime = time.monotonic() - ellapsedTime
    stepConclusion(r'# file_ moved', done, ellapsedTime)



# FURTHER SPLITTING FILES INTO SUB-SUBDIRECTORIES

if (not option_keepDirStructure):
    print(r'Splitting files into subdirectories...', end=r'', flush=True)
    ellapsedTime = time.monotonic()
    ignored = 0
    done = 0
    j = 0
    for subdir in [os.path.join(targetRootDir, d) for d in os.listdir(targetRootDir)]:
        files = [os.path.join(subdir, file) for file in os.listdir(subdir)]
        files = [file for file in files if os.path.isfile(file)]
        if (len(files) <= maxFilesPerDir):
            ignored += len(files)
            continue
        files = split(sorted(files, key=lambda x: fileSize(x)), maxFilesPerDir)
        i = 0
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
                progress(r'Splitting files into subdirectories...', (ignored + done), initialTotal)
        j += i

    ellapsedTime = time.monotonic() - ellapsedTime
    if (j < 2): _clearLine()
    else: stepConclusion(r'# file_ split into ' + str(j) + ' subdirectories', done, ellapsedTime)



# REMOVING EMPTY SUBDIRECTORIES LEFT BEHIND

if (option_wipeEmptyDirs):
    for path, subdirs, items in os.walk(targetRootDir, topdown=False):
        relativeTo = os.path.join(targetRootDir, path)
        for subdir in subdirs:
            try: os.removedirs(os.path.join(relativeTo, subdir))
            except: pass



# FIXING FILE OWNERSHIPS IF RUNNING AS ROOT

if (option_runningWithSudo):
    print('Fixing ownership of files and directories...', end=r'', flush=True)
    for path, subdirs, items in os.walk(targetRootDir):
        for name in items: os.chown(os.path.join(path, name), uid, gid)
        for name in subdirs: os.chown(os.path.join(path, name), uid, gid)



# DONE

print('\rDone!' + (r' ' * 70))
