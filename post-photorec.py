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

import sys, os, re, mmap, codecs, json, gzip, filecmp
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

def error( message, whatToReturn ):
    sys.stderr.write('\x1B[31;1mError: ' + message + '\n')
    exit(whatToReturn)

def progress( message, done, total ):
    progressLen = (len(str(total)) * 2) + 1
    p = str(done) + r'/' + str(total)
    sys.stdout.write('\r' + message + r' ' + p.ljust(progressLen) + ('\b' * (progressLen - len(p))))

def _unmute():
    sys.stderr = sys.__stderr__
    sys.stdout = sys.__stdout__

def _mute():
    try: sys.stderr = sys.stdout = open(os.devnull, r'w')
    except: _unmute()



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
    return re.sub(r'\s+', r' ', unormalize(r'NFC', stringOrStrings.translate(_table)).strip())



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
    return content



# METADATA-TO-FILENAME FUNCTIONS

def nonEXIFImageFilename( image, currentName ):
    return currentName

def imageFilename( image, currentName ):
    try: EXIF = image._getexif()
    except: EXIF = None
    if ((EXIF is None) or (len(EXIF) < 1)):
        try: image.load()
        except: return currentName
        EXIF = image.info.get(r'exif', None)
        if ((EXIF is None) or (len(EXIF) < 1)):
            newFilename = nonEXIFImageFilename(image, currentName)
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
        if ((title is None) or (len(title) < 2)): return currentName
        newFilename = _normalized(author + title + r'.' + os.path.extsplit(currentName)[-1])
    else:
        newFilename = _normalized(cameraModel + r' ' + date + r'.' + os.path.extsplit(currentName)[-1])
    print (newFilename)
    return os.path.join(os.path.split(currentName)[0], newFilename)

def songFilename( parsedInfo, currentName ):
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
    if (len(final) <= 1): return currentName
    path = currentName.rsplit(os.path.sep, 1)[0]
    if (extension == r'mp4'): extension = r'm4a'
    return os.path.join(path, (final + r'.' + os.path.extsplit(currentName)[-1]))

def videoFilename( parsedInfo, currentName ):
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
    if ((len(artist) + len(title)) == 0):
        if (currentName.endswith(res + r'.' + os.path.extsplit(currentName)[-1])): return currentName
        final = currentName.rsplit(os.path.sep, 1)[-1]
        final = _normalized(final.rsplit(r'.', 1)[0] + res)
    if (len(final) <= 1): return currentName
    path = currentName.rsplit(os.path.sep, 1)[0]
    return os.path.join(path, (final + r'.' + os.path.extsplit(currentName)[-1]))

def fontFilename( currentName ):
    if (re.match(r'^.*\.([ot]t[cf]|tte|dfont)$', currentName)):
        try: font = ttLib.TTFont(currentName)
        except: return currentName
    else:
        return currentName
    name = r''
    family = r''
    _mute()
    for record in font[r'name'].names:
        try:
            if (b'\x00' in record.string):
                name_str = record.string.decode(r'utf-16-be')
            else:
                try: name_str = record.string.decode(r'utf-8')
                except: name_str = record.string.decode(r'latin-1')
        except:
            return currentName
        if ((record.nameID == 2) and (not name)): name = name_str
        elif ((record.nameID == 1) and (not family)): family = name_str
        if (name and family): break
    _unmute()
    path = currentName.rsplit(os.path.sep, 1)[0]
    name = _normalized(family + r' ' + name)
    if (len(name) < 2): return currentName
    return os.path.join(path, (name + r'.' + currentName.rsplit(r'.', 1)[-1]))

def torrentFilename( currentName ):
    if (not os.path.isfile(currentName)): return currentName
    with open(currentName, r'rb') as f:
        try: content = f.readline()
        except: return currentName
        content = content.split(b'6:pieces')[0]
        try:
            encoding = cchardet.detect(content)[r'encoding']
            encoding = codecs.lookup(encoding if (encoding is not None) else r'utf-8').name
        except:
            encoding = r'utf-8'
        content = content.decode(encoding, r'ignore')
        name = re.findall(r'4:name([0-9]+):', content)
        if (len(name) == 0): return currentName
        name = re.findall(r'4:name' + name[0] + ':(.{' + name[0] + '})', content)
        if (len(name) == 0): return currentName
        path = currentName.rsplit(os.path.sep, 1)[0]
        return os.path.join(path, (_normalized(name[0]) + r'.torrent'))



# SPECIAL FILE MANIPULATION FUNCTION

def moveNotReplacing( file, toWhere ):
    try:
        newFilename = os.path.join(toWhere, os.path.split(file)[-1])
        os.rename(file, newFilename)
        return newFilename
    except:
        i = 2
        name, ext = os.path.splitext(os.path.split(file)[-1])
        name = os.path.join(toWhere, name)
        while True:
            try:
                newFilename = name + r' (' + str(i) + r').' + ext
                os.rename(file, newFilename)
                return newFilename
            except FileExistsError:
                i += 1
            except:
                return file



# SPLIT FUNCTION

def split( l, chunkMaxSize ):
    for i in range(0, len(l), chunkMaxSize):
        yield l[i:(i + chunkMaxSize)]



# DEFINING FILENAME REGEXES

fontFile = re.compile(r'^.+\.(dfont|woff|[ot]t[cf]|tte)$')
codeFile = r'^.*\.([CcHh](\+\+|pp)|[cejlrt]s|objc|[defmMPrRS]|p(y3?|[lm]|p|as|hp|s1)|s(h|ql|c(ala|ptd?)?)|'
codeFile += r'go|a(sp|d[bs])|c([bq]?l|lj[sc]?|ob(ra)?|py|yp)|li?sp|t(cl|bc)|j(ava|j)|(m|[eh]r)l|l?hs|'
codeFile += r'[rv]b|vhdl?|exs?|dart|applescript|f(or|90)|boo|[jt]sx|va(la|pi)|GAMBAS|(lit)?coffee|'
codeFile = re.compile(codeFile + 'fs([ix]|script)|jl|lua|mm|w?asm|hx(ml)?|g(v|roov)?y|w(l|at)|b(at|tm)|cmd)$')
pictureFile = r'^.*\.(a(n?i|png)|b([lm]p|pg)|d(c[rx]|ds|ib)|e(ps[fi]?|mf)|g(d|if)|i(mt?|co|cns)|flif|vsd|'
pictureFile += r'j(p[2efx]|[np]g|peg|xr)|m(ic|po|sp|ng)|p(c[dx]|ng|[abgnp]m|s[db])|odg|c(in|r2|rw|ur)|'
pictureFile = re.compile(pictureFile + r'[hw]dp|heic|s(gi|vgz?)|t(ga|iff?)|w(al|ebp|mf|bmp|pg)|x([bp]m|cf))$')
ambigMediaFile = re.compile(r'^.*\.(asf|ogg|webm|rm(vb)?|riff|3g(p?[p2]|pp2))$')
videoFile = re.compile('^.*\.(avi|(fl|mq|vi|wm)v|m([4ko]v|p(4|e|e?g))|ogv|qt|rmvb)$')
documentFile = r'^.*\.((f?od|uo)[pst]|o(le|pf)|(xls|ppt|doc)x?|p(df|s|ps)|g(p[345x]?|tp)|tg|css|'
documentFile = re.compile(documentFile + r'e(nc|pub)|[a-z]?html?(\.gz)?|m(obi|d)|djvu?|chm|rtf|[tc]sv|dcx)$')
audioFile = r'^.*\.(m(4[abp]|ka|p[+c123]|idi?)|w(ma|a?v)|flac|a(ac|c3|pe|u)|dts|oga|tta|gsm|'
audioFile = re.compile(audioFile + r'ra|ofr|s(px|nd))$')



# PROCESSING COMMAND LINE ARGUMENTS

targetRootDir = None
for arg in sys.argv:
    if (os.path.isdir(arg)):
        if (targetRootDir is None): targetRootDir = arg
        else: error("More than one path passed as argument", 2)
if (r'-Q' in sys.argv): # Not-so-verbose mode (no progress output)
    def progress( message, done, total ): pass
if (r'-q' in sys.argv): # Quiet mode (no verbosity at all)
    def progress( message, done, total ): pass
    def print( *args ): pass
    def _unmute(): sys.stderr = sys.__stderr__
    sys.stdout = open(os.devnull, r'w')
option_removeKnownJunk = r'-J' not in sys.argv # Do not remove junk files
if (r'-J' in sys.argv):
    def removeJunkFile( filePath ): pass
else:
    def removeJunkFile( filePath ): os.remove(filePath)
option_removeDuplicates = r'-D' not in sys.argv # Do not remove duplicate files
option_keepDirStructure = r'-k' in sys.argv # Keep Directory Structure



# GENERATING THE LIST OF FILES TO BE PROCESSED

sys.stdout.write(r'Listing files...')
files = []
for path, subdirs, items in os.walk(targetRootDir):
    files += [os.path.join(path, name) for name in items]
initialTotal = len(files)
print('\r' + str(initialTotal) + ' files found' + (r' ' * 20) + ('\b' * 20))



# REMOVING EMPTY FILES

sys.stdout.write(r'Removing empty files...')
files = [(os.stat(file).st_size, os.path.splitext(file)[-1], file) for file in files]
files = sorted(files)
j = 0
if (files[0][0] == 0):
    for i in range(0, len(files)):
        if (files[i][0] != 0): break
        j += 1
    for i in range(0, j):
        progress(r'Removing empty files...', (j - (j - i)), j)
        os.remove(files[i][2])
        files[i] = (0, r'', files[i][2])
print('\r' + str(j) + ' empty files removed' + (r' ' * 20) + ('\b' * 20))



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
                if (filecmp.cmp(files[i][2], files[j][2], shallow=False)):
                    actuallyDeduped += 1
                    progress(r'Deduplicating files...', (actuallyDeduped + done), initialTotal)
                    os.remove(files[j][2])
                    files[j] = (0, r'', files[j][2])
        done += 1
        progress(r'Deduplicating files...', (actuallyDeduped + done), initialTotal)
    print('\r' + str(actuallyDeduped) + ' duplicates removed' + (r' ' * 20) + ('\b' * 20))




# STARTING TO PROCESS FILES

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



# IMPROVING SOME FILENAMES PHOTOREC SOMETIMES PROVIDES

prenamedFile = r'^f[0-9]{5,}_(.*)[._](([DdRr][Ll][Ll]|[Ee][Xx][Ee])(_[Mm][Uu][Ii])?|'
prenamedFile += r'[Dd]2[Ss]|[Zz][Ii][Pp]|[Ss][Yy][Ss]|'
prenamedFile = re.compile(prenamedFile + '[Dd][Oo][Cc]|[Pp][Dd][Ff])$')
def fixedPhotoRecName( match ):
    return match.group(1) + r'.' + match.group(2).lower().replace(r'_', r'.')
for i in range(0, len(files)):
    filename = files[i].rsplit(os.path.sep, 1)[-1]
    if (prenamedFile.match(filename)):
        newFilename = prenamedFile.sub(fixedPhotoRecName, filename)
        newFilename = os.path.join(os.path.split(files[i])[0], newFilename)
        os.rename(files[i], newFilename)
        files[i] = newFilename



# REMOVING UNSUPPORTED FILES FROM THE LIST

unsupportedFormats = re.compile(r'^.*\.(d2s|sys|[ao]|json(lz4)?|class|m3u|pyc)$')
files = [file for file in files if not unsupportedFormats.match(file)]
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
            content = decodedFileContent(f).strip()
            lineCount = content.count('\n')
            if ((lineCount > 6) and
                ((len(logLine1.findall(content)) >= (lineCount - 1)) or
                (len(logLine2.findall(content)) >= (lineCount - 1)) or
                (len(logLine3.findall(content)) >= (lineCount - 1)))):
                os.rename(files[i], (files[i][:-4] + r'.log'))
                done += 1
            elif (content.startswith(r'<?xml')):
                os.rename(files[i], (files[i][:-4] + r'.xml'))
                buffer.append(files[i][:-4] + r'.xml')
            elif (len(srtTime.findall(content)) > max(1, (lineCount / 8))):
                os.rename(files[i], (files[i][:-4] + r'.srt'))
                buffer.append(files[i][:-4] + r'.srt')
            elif ((r'<!-- Created with Inkscape (http://www.inkscape.org/) -->' in content) and
                (r'</svg>' in content)):
                os.rename(files[i], (files[i][:-4] + r'.svg'))
                buffer.append(files[i][:-4] + r'.svg')
            elif (len(tclLine.findall(content)) > 0):
                os.rename(files[i], (files[i][:-4] + r'.tcl'))
                buffer.append(files[i][:-4] + r'.tcl')
            else:
                done += 1
                if (maybeJSON.match(content)):
                    try:
                        junk = json.loads(content)
                        os.rename(files[i], (files[i][:-4] + r'.json'))
                        del junk
                        continue
                    except:
                        pass
                gpd_pcfName = gpd_pcfNameLine.findall(content)
                if (len(gpd_pcfName) == 1):
                    newFilename = _normalized(gpd_pcfName[0][1])
                    newFilename = re.sub(r'(\.[GgPp][Pp][Dd])$', lambda x: x.group(0).lower(), newFilename)
                    newFilename = os.path.join(os.path.split(files[i])[0], newFilename)
                    os.rename(files[i], newFilename)
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
            content = decodedFileContent(f).strip()
            lineCount = content.count('\n')
            if (content.startswith(r'[Script Info]')):
                if (len(ssaLine.findall(content)) > max(1, ((lineCount / 3) - 25))):
                    os.rename(files[i], (files[i][:-4] + r'.ass'))
                    buffer.append(files[i][:-4] + r'.ass')
                else:
                    buffer.append(files[i])
            elif (content.startswith(r'[General]\s*\n\s*Version=DrumSynth v2\.0')):
                os.rename(files[i], (files[i][:-4] + r'.ds'))
                done += 1
            elif (content.startswith(r'[MIME Cache]')):
                removeJunkFile(files[i])
            elif (content.startswith(r'[Desktop Entry]')):
                newFilename = desktopEntryNameLine1.findall(content)
                if (len(newFilename) < 1):
                    newFilename = desktopEntryNameLine2.findall(content)
                    if (len(newFilename) < 1):
                        newFilename = files[i][:-4]
                    else:
                        newFilename = _normalized(re.sub(r'\s+', r'-', newFilename[0].lower()))
                        newFilename = os.path.join(os.path.split(files[i])[0], newFilename)
                else:
                    newFilename = _normalized(os.path.split(newFilename[0])[-1])
                    newFilename = os.path.join(os.path.split(files[i])[0], newFilename)
                os.rename(files[i], (newFilename + r'.desktop'))
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
                os.rename(files[i], (files[i][:-5] + r'.cs'))
                files[i] = files[i][:-5] + r'.cs'
    elif (files[i].endswith(r'.c')):
        with open(files[i], r'rb') as f:
            content = cStrings.sub('\x22\x22', cComments.sub(r'', decodedFileContent(f)))
            if (len(cppLine.findall(content)) > 0):
                os.rename(files[i], (files[i][:-5] + r'.cpp'))
                files[i] = files[i][:-5] + r'.cpp'
    if (files[i].endswith((r'.cs', r'java'))):
        done += 1
        progress(r'Analyzing files...', done, initialTotal)
        with open(files[i], r'rb') as f:
            content = decodedFileContent(f)
            pkg = packageName.findall(content)
            name = className.findall(content)
            if (len(name) != 1): continue
            newFilename = _normalized(name[0][1]) + r'.' + files[i].rsplit(r'.', 1)[-1]
            if (len(pkg) == 1): newFilename = _normalized(pkg[0]) + r'.' + newFilename
            newFilename = os.path.join(os.path.split(files[i])[0], newFilename)
            os.rename(files[i], newFilename)
    else:
        buffer.append(files[i])
files = buffer



# NAMING IMAGE FILES

buffer = []
for i in range(0, len(files)):
    if (pictureFile.match(files[i])):
        done += 1
        progress(r'Analyzing files...', done, initialTotal)
        try:
            image = Image.open(files[i], r'r')
            newFilename = imageFilename(image, files[i])
            os.rename(files[i], newFilename)
        except:
            continue
    else:
        buffer.append(files[i])
files = buffer



# NAMING MEDIA FILES

buffer = []
for i in range(0, len(files)):
    if (files[i].endswith(r'.mp4')):
        done += 1
        progress(r'Analyzing files...', done, initialTotal)
        try:
            av = MediaInfo.parse(files[i])
            isM4A = True
            for track in av.tracks:
                if (track.track_type[0] == r'V'):
                    isM4A = False
                    break
            if (isM4A): newFilename = songFilename(av, files[i])
            else: newFilename = videoFilename(av, files[i])
            os.rename(files[i], newFilename)
        except:
            continue
    elif (files[i].endswith(r'.m4a')):
        done += 1
        progress(r'Analyzing files...', done, initialTotal)
        try:
            av = MediaInfo.parse(files[i])
            newFilename = songFilename(av, files[i])
            os.rename(files[i], newFilename)
        except:
            continue
    else:
        buffer.append(files[i])
files = buffer

buffer = []
for i in range(0, len(files)):
    if (audioFile.match(files[i])):
        done += 1
        progress(r'Analyzing files...', done, initialTotal)
        try:
            av = MediaInfo.parse(files[i])
            newFilename = songFilename(av, files[i])
            os.rename(files[i], newFilename)
        except:
            continue
    else:
        buffer.append(files[i])
files = buffer

buffer = []
for i in range(0, len(files)):
    if (videoFile.match(files[i])):
        done += 1
        progress(r'Analyzing files...', done, initialTotal)
        try:
            av = MediaInfo.parse(files[i])
            newFilename = videoFilename(av, files[i])
            os.rename(files[i], newFilename)
        except:
            continue
    else:
        buffer.append(files[i])
files = buffer



# NAMING DOCUMENT FILES

buffer = []
for i in range(0, len(files)):
    if (files[i].endswith(r'.pdf')):
        done += 1
        progress(r'Analyzing files...', done, initialTotal)
        try: document = PDFFile(files[i], strict=False)
        except: continue
        try:
            if (document.isEncrypted): continue
            info = document.documentInfo
            if (info is None): continue
            author = info.get(r'/Author', r'')
            if (isinstance(author, PDFIndirectObject)): author = document.getObject(author)
            author = _normalized(author + r' - ') if (author is not None) else r''
            title = info.get(r'/Title', r'')
            if (isinstance(title, PDFIndirectObject)): title = document.getObject(title)
            if ((title is None) or (len(title) <= 1)): continue
            title = _normalized(title)
            newFilename = _normalized(author + title) + r'.pdf'
            newFilename = os.path.join(os.path.split(files[i])[0], newFilename)
            os.rename(files[i], newFilename)
        except:
            continue
    else:
        buffer.append(files[i])
files = buffer

oleFile = re.compile(r'^.+\.(doc|xls|ppt|ole)$')
openxmlFile = re.compile(r'^.+\.(doc|xls|ppt)x$')
odFile = re.compile(r'^.+\.f?od[gpst]$')
buffer = []
for i in range(0, len(files)):
    if (oleFile.match(files[i])):
        done += 1
        progress(r'Analyzing files...', done, initialTotal)
        try:
            document = OLEFile(files[i])
            documentMetadata = document.get_metadata()
            document.close()
        except:
            continue
        encoding = documentMetadata.codepage
        encoding = documentMetadata.codepage if ((encoding is not None) and (encoding > 0)) else 1252
        encoding = r'cp' + str(encoding)
        author = r''
        if ((documentMetadata.author is not None) and (len(documentMetadata.author) > 1)):
            author = r' (' + documentMetadata.author.decode(encoding) + r')'
        if ((documentMetadata.title is not None) and (len(documentMetadata.title) > 1)):
            title = _normalized(documentMetadata.title.decode(encoding))
            newFilename = _normalized(title + author) + r'.' + files[i].rsplit(r'.', 1)[-1]
            newFilename = os.path.join(os.path.split(files[i])[0], newFilename)
            os.rename(files[i], newFilename)
    elif (openxmlFile.match(files[i])):
        done += 1
        progress(r'Analyzing files...', done, initialTotal)
        try: document = ZIPFile(files[i], r'r')
        except: continue
        try:
            XMLMetadataFile = document.open(r'docProps/core.xml')
            parsedXML = _parsedXML(XMLMetadataFile)
            if (parsedXML is None): continue
            field = parsedXML.find('//creator')
            author = (r' (' + field.text + r')') if (field is not None) else r''
            field = parsedXML.find('//title')
            if ((field is not None) and (len(field.text) > 1)): title = field.text
            else: continue
            XMLMetadataFile.close()
            newFilename = _normalized(title + author) + r'.' + files[i].rsplit(r'.', 1)[-1]
            newFilename = os.path.join(os.path.split(files[i])[0], newFilename)
            os.rename(files[i], newFilename)
        except:
            pass
    elif (odFile.match(files[i])):
        done += 1
        progress(r'Analyzing files...', done, initialTotal)
        with open(files[i], r'rb') as document:
            fileSignature = document.read(2)
            document.seek(0)
            if (fileSignature == b'<?'):
                try: parsedXML = _parsedXML(document)
                except: continue
            else:
                try: XMLMetadataFile = ZIPFile(files[i], r'r').open(r'meta.xml')
                except: continue
                parsedXML = _parsedXML(XMLMetadataFile)
            if (parsedXML is None): continue
            field = parsedXML.find(r'//initial-creator')
            if (field is None): field = parsedXML.find(r'//creator')
            author = (r' (' + field.text + r')') if (field is not None) else r''
            field = parsedXML.find(r'//title')
            if ((field is not None) and (len(field.text) > 1)): title = field.text
            else: continue
            newFilename = _normalized(title + author) + r'.' + files[i].rsplit(r'.', 1)[-1]
            newFilename = os.path.join(os.path.split(files[i])[0], newFilename)
            os.rename(files[i], newFilename)
    else:
        buffer.append(files[i])
files = buffer

htmlFile = re.compile(r'^.+\.[a-z]?html?$')
buffer = []
for i in range(0, len(files)):
    if (htmlFile.match(files[i])):
        done += 1
        progress(r'Analyzing files...', done, initialTotal)
        try: xml = html.parse(files[i])
        except: continue
        title = xml.find(r'.//title')
        if (title is None):
            title = xml.find(r'.//meta[@name="title"]')
            if (title is None): title = xml.find(r'.//meta[@property="og:title"]')
            if (title is None): title = xml.find(r'.//meta[@name="parsely-title"]')
            if (title is None): title = xml.find(r'.//name')
        if (title is not None): title = title.text
        else: continue
        newFilename = _normalized(title) + r'.' + files[i].rsplit(r'.', 1)[-1]
        newFilename = os.path.join(os.path.split(files[i])[0], newFilename)
        os.rename(files[i], newFilename)
    else:
        buffer.append(files[i])
files = buffer



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
        newFilename = _normalized(title) + r'.html.gz'
        newFilename = os.path.join(os.path.split(files[i])[0], newFilename)
        os.rename(files[i], newFilename)
    elif (files[i].endswith(r'.gz')):
        try:
            gz = gzip.open(files[i], r'rb')
        except:
            removeJunkFile(files[i])
    else:
        buffer.append(files[i])
files = buffer



# NAMING FONT FILES

buffer = []
for i in range(0, len(files)):
    if (fontFile.match(files[i])):
        done += 1
        progress(r'Analyzing files...', done, initialTotal)
        newFilename = fontFilename(files[i])
        os.rename(files[i], newFilename)
    else:
        buffer.append(files[i])
files = buffer



# NAMING TORRENT FILES

buffer = []
for i in range(0, len(files)):
    if (files[i].endswith(r'.torrent')):
        done += 1
        progress(r'Analyzing files...', done, initialTotal)
        newFilename = torrentFilename(files[i])
        os.rename(files[i], newFilename)
    else:
        buffer.append(files[i])
files = buffer



# NAMING PLAYLIST AND CUE FILES

buffer = []
for i in range(0, len(files)):
    if (files[i].endswith(r'.wpl')):
        done += 1
        progress(r'Analyzing files...', done, initialTotal)
        with open(files[i], r'rb') as f:
            title = re.findall(r'<title>.*</title>', decodedFileContent(f))
            if ((len(title) > 0) and (len(title[0]) > 0)):
                newFilename = _normalized(re.sub(r'<title>(.*)</title>', r'\1', title[0]))
                newFilename += r'.wpl'
                newFilename = os.path.join(os.path.split(files[i])[0], newFilename)
                os.rename(files[i], newFilename)
    elif (files[i].endswith(r'.cue')):
        done += 1
        progress(r'Analyzing files...', done, initialTotal)
        with open(files[i], r'rb') as f:
            content = decodedFileContent(f)
            title = re.findall('\nTITLE \x22(.*)\x22', content)
            if ((len(title) == 0) or (len(title[0]) == 0)):
                title = re.findall('\nFILE \x22(.*)\.[a-zA-Z0-9+]{1,4}\x22', content)
                if ((len(title) == 0) or (len(title[0]) == 0)): continue
                else: title = title[0]
            else:
                title = title[0]
                artist = re.findall('\nPERFORMER \x22(.*)\x22', content)
                if ((len(artist) > 0) and (len(artist[0]) > 0)):
                    title = artist[0] + r' - ' + title
            newFilename = _normalized(title) + r'.cue'
            newFilename = os.path.join(os.path.split(files[i])[0], newFilename)
            os.rename(files[i], newFilename)
    else:
        buffer.append(files[i])
files = buffer



# SOME VERBOSITY

print('\r' + str(done) + ' files analyzed' + (r' ' * 20) + ('\b' * 20))



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



# FURTHER SPLITTING FILES INTO SUB-SUBDIRECTORIES

if (not option_keepDirStructure):
    maxFilesPerDir = 250
    for subdir in [os.path.join(targetRootDir, d) for d in os.listdir(targetRootDir)]:
        files = [os.path.join(subdir, file) for file in os.listdir(subdir)]
        files = [file for file in files if os.path.isfile(file)]
        if (len(files) <= maxFilesPerDir): continue
        files = split(sorted(files, key=lambda x: os.stat(x).st_size), maxFilesPerDir)
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



# REMOVING EMPTY SUBDIRECTORIES LEFT BEHIND

for path, subdirs, items in os.walk(targetRootDir):
    try: os.rmdir(path)
    except: pass



# SOME VERBOSITY

if (not option_keepDirStructure):
    print('\r' + str(done) + ' files moved' + (r' ' * 20) + ('\b' * 20))
print('Done!')
