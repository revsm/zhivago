///////////////////////////////////////////////////////////////////////////
// ZHIVAGO - Website Malware Scanner
///////////////////////////////////////////////////////////////////////////

// Based on AI-BOLIT originally created by Greg Zemkov, Revisium Company
// GO version developer: Pavel Gryaznov http://github.com/GRbit
//
// Email: ai@revisium.com, http://revisium.com/zhivago/, skype: greg_zemskov

// Free for non-commercial usage only. License purchase is required for commercial usage.
// Neither source code snippets nor signature database are allowed to use in other products without
// written permission of the product owner.

////////////////////////////////////////////////////////////////////////////
// Версия сканера AI-BOLIT на языке GO
// Программирование версии на GO: Павел Грязнов http://github.com/GRbit
//
// Запрещено использование скрипта в коммерческих целях без приобретения лицензии.
// Запрещено использование исходного кода скрипта и сигнатур без письменного разрешения владельца.
//
// По вопросам приобретения лицензии обращайтесь в компанию "Ревизиум": http://www.revisium.com
// ai@revisium.com
///////////////////////////////////////////////////////////////////////////

package main

import (
	"flag"
	"fmt"
	"hash/crc32"
	"io/ioutil"
	"log"
	"math"
	"math/rand"
	"net/mail"
	"os"
	"path/filepath"
	"regexp"
	"runtime"
	"strconv"
	"strings"
	"sync"
	//"syscall"
	"time"

	"github.com/GRbit/go-pcre"
	"github.com/djherbis/times"
	"github.com/xurenlu/ahocorasick"
)

const (
	// put 1 for expert mode, 0 for basic check and 2 for paranoic mode

	gExpertMode     = 2
	gZhivagoVersion = "20151028"
	gDebugMode      = false
	gAsyncMode      = true

	gMaxPHPandHTML = 600
	gMaxPreviewLen = 80
	gMaxExtLinks   = 1001
)

// <GLOBALS>
var (
	timeCounter int64 = 0

	gSuspiciousFiles = []string{"cgi", "pl", "o", "so", "py", "sh", "phtml", "php3", "php4", "php5", "shtml", "suspicious"}
	gSensitiveFiles  = append(gSuspiciousFiles, "php", "js", "htaccess", "html", "htm", "tpl", "inc", "css", "txt", "sql")
	gCriticalFiles   = []string{"php", "htaccess", "cgi", "pl", "o", "so", "py", "sh", "phtml", "php3", "php4", "php5", "shtml", "suspicious"}
	gCriticalEntries = pcreCompile("<?php|<?=|#!/usr|#!/bin|eval|assert|base64_decode|system|create_function|exec|popen|fwrite|fputs|file_get_|calluser_func|file_put_|$_REQUEST|ob_start|$_GET|$_POST|$_SERVER|$_FILES|move|copy|array_|regreplace|mysql_|fsockopen|$GLOBALS|sqliteCreateFunction", 0).Matcher([]byte{}, 0)
	gVirusFiles      = []string{"js", "html", "htm", "suspicious"}
	gVirusEntries    = pcreCompile("<\\s*script|<\\s*iframe|<\\s*object|<\\s*embed|setTimeout|setInterval|location\\.|document\\.|window\\.|navigator\\.|\\$(this)\\.", 0).Matcher([]byte{}, 0)
	gPhishFiles      = []string{"js", "html", "htm", "suspicious", "php"}
	gPhishEntries    = pcreCompile("<\\s*title|<\\s*html|<\\s*form|<\\s*body", 0).Matcher([]byte{}, 0)
	gShortListExt    = []string{"php", "php3", "php4", "php5", "html", "htm", "phtml", "shtml", "khtml"}

	//malware regexp arrays
	gSusDB, gFlexDBShe, gX_FlexDBShe, gXX_FlexDBShe, gExceptFlex, gAdwareSig, gPhishingSig, gJSVirSig, gX_JSVirSig []SignedRegexp

	gDBShe   = ahocorasick.NewMatcher()
	gX_DBShe = ahocorasick.NewMatcher()

	gIgnoredFiles, gIgnoredUrl, gIgnoredExt, gIgnoredDir                          []string
	gBase64, gDoorway, gSymLinks, gUnixExec, gHiddenFiles, gBigFiles, gVulnerable []string

	gKnownList = make(map[int]bool)

	gFoundTotalDirs = 0

	absPath, _ = os.Getwd()

	def = Settings{
		path:          absPath,
		scanAllFiles:  true, // full scan (rather than just a .js, .php, .html, .htaccess)
		smartScan:     true,
		threads:       runtime.NumCPU() - 1,
		maxSizeToScan: getBytes("600K"),
		reportPath:    absPath,
		skipExt:       "",
		host:          "",
		extraWarn:     false,
		expertMode:    gExpertMode,
	}

	DoubleCheckFile = "ZHIVAGO-DOUBLECHECK"
	gPathSep        = string(os.PathSeparator)
	gQueueToScan    []string

	// report globals
	gTotalOutput = Output{}
	gColorRed    = "\x1b\x5b\x31\x3b\x33\x31\x6d"
	gColorOff    = "\x1b\x5b\x6d"

	// regexp globals
	// SearchPHP
	phpRegexp       = pcreCompile("(?smi)(<\\?php[\\w\\s]{5,})", 0)
	phpScriptRegexp = pcreCompile("(?i)(<script[^>]*language\\s*=\\s*)('|\"|)php('|\"|)([^>]*>)", 0)

	// php_strip
	rComment1 = pcreCompile(`(?m)^[\s]*//.*$`, 0)
	rComment2 = pcreCompile(`(?s)/\*.*?\*/`, 0)
	// unwrapObfu
	allToSpace     = strings.NewReplacer("\t", " ", "\x09", " ", "\x0A", " ", "\x0B", " ", "\x0C", " ", "\x0D", " ")
	excessiveSpace = strings.NewReplacer(
		" ;", ";", "; ", ";",
		" =", "=", "= ", "=",
		" ,", ",", ", ", ",",
		" .", ".", ". ", ".",
		" (", "(", "( ", "(",
		" )", ")", ") ", ")",
		" {", "{", "{ ", "{",
		" }", "}", "} ", "}",
		" +", "+", "+ ", "+",
	)
	rChrItnVal = regexp.MustCompile(`\bchr ?\( ?([0-9a-fA-FxX]+) ?\)`)
	rEscHex    = regexp.MustCompile(`\\x([0-9a-fA-F]{1,2})`)
	rEscDec    = regexp.MustCompile(`\\([0-9]{1,3})`)

	// unwraObfu; this one need to be build additionaly like in func prepare()
	tonnsOfSpaces = []string{}
	singleSpace   = strings.NewReplacer(tonnsOfSpaces...)

	// CriticalPHP
	rCopy = pcreCompile(`(?smi)\bcopy\s*\(`, 0)
)

// </GLOBALS>

type Output struct {
	crit  string
	js    string
	other string
	all   []string
}
type OffsetMatch struct {
	str   string
	index int
}
type StructureElement struct {
	name  string
	size  int64
	mtime int64
	ctime int64
	crc   int
}
type Settings struct {
	path          string
	scanAllFiles  bool
	smartScan     bool
	threads       int
	maxSizeToScan int
	reportPath    string
	skipExt       string
	host          string
	extraWarn     bool
	expertMode    int
}
type SignedRegexp struct {
	regexp pcre.Regexp
	text   string
	sign   string
}

func getExt(path string) string {
	ext := filepath.Ext(path)
	if ext == "" {
		ext = filepath.Base(path)
	} else {
		ext = ext[1:]
	}
	return strings.ToLower(ext)
}
func realpath(path string) string {
	path, err := filepath.EvalSymlinks(path)
	path, err = filepath.Abs(path)
	if err != nil {
		log.Println("Can't get realpath, ERR:")
		log.Fatalln(err)
	}
	return path
}

func writable(path string) error {
	info, err := os.Stat(path)
	if (err != nil) && ((info.Mode() & 0333) != 0) {
		return nil
	}
	return err
}

func stripos(haystack, needle string) bool {
	needle = strings.ToLower(needle)
	haystack = strings.ToLower(haystack)
	return strings.Contains(haystack, needle)
}

func pcreFlags(r string) (string, int) {
	flags := 0
	for fStr := regexp.MustCompile("^\\(\\?[a-zA-Z]+\\)").FindString(r); // init
	fStr != "";                                                          // if something found
	r = r[len(fStr):] {                                                  // decrease orig string
		fStr = regexp.MustCompile("^\\(\\?[a-zA-Z]+\\)").FindString(r)
		if strings.Contains(fStr, "i") {
			flags = flags | pcre.CASELESS
		}
		if strings.Contains(fStr, "D") {
			flags = flags | pcre.DOLLAR_ENDONLY
		}
		if strings.Contains(fStr, "s") {
			flags = flags | pcre.DOTALL
		}
		if strings.Contains(fStr, "J") {
			flags = flags | pcre.DUPNAMES
		}
		if strings.Contains(fStr, "x") {
			flags = flags | pcre.EXTENDED
		}
		if strings.Contains(fStr, "X") {
			flags = flags | pcre.EXTRA
		}
		if strings.Contains(fStr, "m") {
			flags = flags | pcre.MULTILINE
		}
		if strings.Contains(fStr, "U") {
			flags = flags | pcre.UNGREEDY
		}
		if strings.Contains(fStr, "u") {
			flags = flags | pcre.UTF8
		}
	}
	return r, flags
}

func pcreCompile(r string, f int) pcre.Regexp {
	r, flags := pcreFlags(r)
	flags = flags | f
	retRegex, err := pcre.CompileJIT(r, flags)
	if err != nil {
		log.Println("Can't compile/study pcre regexp: ", r, "\nFlags:", flags)
		log.Fatalln(err)
	}
	return retRegex
}

func fileExists(filename string) bool {
	if _, err := os.Stat(filename); os.IsNotExist(err) {
		return false
	} else if err == nil {
		return true
	}
	return false
}

func stringInArray(a string, list []string) bool {
	if (a == "") || len(list) == 0 {
		return false
	}
	for _, b := range list {
		if b == a {
			return true
		}
	}
	return false
}

func checkRegexpArray(arr []SignedRegexp, subj string, sign *string) (int, string) {
	for _, i := range arr {
		if pos := i.regexp.FindIndex([]byte(subj), 0); pos != nil {
			if !checkException([]byte(subj), pos[0]) {
				*sign = i.sign
				return pos[0], i.text
			}
		}
	}
	return -1, ""
}

func pregVersion(filename, rStr string) string {
	version := "0.0"
	r, err := regexp.Compile("(?smi)" + rStr)
	if err != nil {
		log.Println("Can't compile regexp ", rStr, "ERR:")
		log.Fatalln(err)
	}
	f_bytes, err := ioutil.ReadFile(filename)
	if err != nil {
		log.Println("Can't read ", filename, "ERR:")
		log.Fatalln(err)
	}
	f := string(f_bytes)
	if r.MatchString(f) {
		version = r.FindStringSubmatch(f)[1]
	}
	return version
}

type CmsVersionDetector struct {
	rootPath string
	versions []string
	types    []string
}

func (cvd *CmsVersionDetector) getCmsNumber() int {
	return len(cvd.types)
}
func (cvd *CmsVersionDetector) getCmsName(index int) string {
	return cvd.types[index]
}
func (cvd *CmsVersionDetector) getCmsVersion(index int) string {
	return cvd.versions[index]
}

func (cvd *CmsVersionDetector) addCms(cms_type, cms_version string) {
	cvd.types = append(cvd.types, cms_type)
	cvd.versions = append(cvd.versions, cms_version)
}

func (cvd *CmsVersionDetector) detect() {
	cmsBitrix := "Bitrix"
	cmsWordpress := "Wordpress"
	cmsJoomla := "Joomla"
	cmsDle := "Data Life Engine"
	cmsIpb := "Invision Power Board"
	cmsWebasyst := "WebAsyst"
	cmsOscommerce := "OsCommerce"
	cmsDrupal := "Drupal"
	cmsModx := "MODX"
	cmsInstantcms := "Instant CMS"
	cmsPhpbb := "PhpBB"
	cmsVbulletin := "vBulletin"
	cmsShopscript := "PHP ShopScript Premium"
	cmsVersionUndefined := "0.0"

	if cvd.rootPath != "" {
		cvd.rootPath = def.path
	}

	version := cmsVersionUndefined

	// Bitrix check
	if fileExists(cvd.rootPath + "/bitrix") {
		version = pregVersion(
			cvd.rootPath+"/bitrix/modules/main/classes/general/version.php",
			"define\\(\"SM_VERSION\",\"(.+?)\"\\)")
		cvd.addCms(cmsBitrix, version)
	}

	// WordPress check
	if fileExists(cvd.rootPath + "/wp-admin") {
		version = pregVersion(
			cvd.rootPath+"/wp-includes/version.php",
			"\\$wp_version\\s*=\\s*'(.+?)'")
		cvd.addCms(cmsWordpress, version)
	}

	// Joomla check
	if fileExists(cvd.rootPath + "/libraries/joomla") {
		// for 1.5.x
		version = pregVersion(
			cvd.rootPath+"/libraries/joomla/version.php",
			"var\\s+\\$RELEASE\\s*=\\s*'(.+?)'")
		subversion := pregVersion(
			cvd.rootPath+"/libraries/joomla/version.php",
			"var\\s+\\$DEV_LEVEL\\s*=\\s*'(.+?)'")
		version += "." + subversion

		// for 1.7.x
		version = pregVersion(
			cvd.rootPath+"/includes/version.php",
			"public\\s+\\$RELEASE\\s*=\\s*'(.+?)'")
		subversion = pregVersion(
			cvd.rootPath+"/includes/version.php",
			"public\\s+\\$DEV_LEVEL\\s*=\\s*'(.+?)'")
		version += "." + subversion

		// for 2.5.x and 3.x
		version = pregVersion(
			cvd.rootPath+"/libraries/cms/version/version.php",
			"public\\s+\\$RELEASE\\s*=\\s*'(.+?)'")
		subversion = pregVersion(
			cvd.rootPath+"/libraries/cms/version/version.php",
			"public\\s+\\$DEV_LEVEL\\s*=\\s*'(.+?)'")
		version += "." + subversion

		cvd.addCms(cmsJoomla, version)
	}

	// DLE check
	if fileExists(cvd.rootPath + "/engine/engine.php") {
		version = pregVersion(
			cvd.rootPath+"/engine/data/config.php",
			"'version_id'\\s*=>\\s*\"(.+?)\"")
		version = pregVersion(
			cvd.rootPath+"/install.php",
			"'version_id'\\s*=>\\s*\"(.+?)\"")

		cvd.addCms(cmsDle, version)
	}

	// IPB check
	if fileExists(cvd.rootPath + "/ips_kernel") {
		version = pregVersion(
			cvd.rootPath+"/ips_kernel/class_xml.php",
			"IP.Board\\s+v([0-9\\.]+)")

		cvd.addCms(cmsIpb, version)
	}

	//WebAssyst check
	if fileExists(cvd.rootPath + "/wbs/installer") {
		version = pregVersion(
			cvd.rootPath+"/license.txt",
			"v([0-9\\.]+)")
		cvd.addCms(cmsWebasyst, version)
	}

	//OsCommerce check
	if fileExists(cvd.rootPath + "/includes/version.php") {
		version = pregVersion(
			cvd.rootPath+"/includes/version.php",
			"([0-9\\.]+)")
		cvd.addCms(cmsOscommerce, version)
	}

	//Drupal check
	if fileExists(cvd.rootPath + "/sites/all") {
		version = pregVersion(
			cvd.rootPath+"/CHANGELOG.txt",
			"Drupal\\s+([0-9\\.]+)")
		cvd.addCms(cmsDrupal, version)
	}

	//MODx check
	if fileExists(cvd.rootPath + "/manager/assets") {
		// no way to pick up version
		cvd.addCms(cmsModx, cmsVersionUndefined)
	}

	//Instantcms check
	if fileExists(cvd.rootPath + "/plugins/p_usertab") {
		version = pregVersion(
			cvd.rootPath+"/index.php",
			"InstantCMS\\s+v([0-9\\.]+)")
		cvd.addCms(cmsInstantcms, version)
	}

	//phpBB check
	if fileExists(cvd.rootPath + "/includes/acp") {
		version = pregVersion(
			cvd.rootPath+"/config.php",
			"phpBB\\s+([0-9\\.x]+)")
		cvd.addCms(cmsPhpbb, version)
	}

	//phpBB check
	if fileExists(cvd.rootPath + "/core/admincp") {
		version = pregVersion(
			cvd.rootPath+"/core/api.php",
			"vBulletin\\s+([0-9\\.x]+)")
		cvd.addCms(cmsVbulletin, version)
	}

	//ShopScript check
	if fileExists(cvd.rootPath + "/install/consts.php") {
		version = pregVersion(
			cvd.rootPath+"/install/consts.php",
			"STRING_VERSION',\\s*'(.+?)'")
		cvd.addCms(cmsShopscript, version)
	}
}

func realCRC(subj string) int {
	crc32Limit := math.Pow(2, 31) - 1
	crc32Diff := crc32Limit*2 - 2

	h := crc32.NewIEEE()
	h.Write([]byte(subj))
	s := float64(h.Sum32())
	var crc int
	if s > crc32Limit {
		crc = int(int64(s) - int64(crc32Diff))
	} else {
		crc = int(s)
	}
	return crc
}

func myCheckSum(subj string) string {
	return strings.Replace(fmt.Sprint(realCRC(subj)), "-", "x", 1)
}

func getEmails(subj string) []string {
	emails := regexp.MustCompile("[,\\s;]").Split(subj, -1)
	verified_emails := []string{}
	for _, e := range emails {
		e, err := mail.ParseAddress(e)
		if err == nil {
			verified_emails = append(verified_emails, e.Address)
		}
	}
	return verified_emails
}

func getBytes(val string) int {
	val = strings.TrimSpace(strings.ToLower(val))
	bytes, err := strconv.Atoi(val[0 : len(val)-1])
	if err != nil {
		log.Println("getBytes, bytes string is incorrect\n", err)
		return 0
	}
	last := val[len(val)-1]
	switch last {
	case 't':
		bytes *= 1024 * 1024 * 1024 * 1024
	case 'g':
		bytes *= 1024 * 1024 * 1024
	case 'm':
		bytes *= 1024 * 1024
	case 'k':
		bytes *= 1024
	}
	return bytes
}

func bytes2Human(bytes int) string {
	var ret string
	if bytes < 1024 {
		ret = strconv.Itoa(bytes) + " b"
	} else if kb := bytes / 1024; kb < 1024 {
		ret = strconv.Itoa(int(kb)) + " Kb"
	} else if mb := kb / 1024; mb < 1024 {
		ret = strconv.Itoa(int(mb)) + " Mb"
	} else if gb := mb / 1024; gb < 1024 {
		ret = strconv.Itoa(int(gb)) + " Gb"
	}
	return ret
}

func isDoorway(path string) bool {
	ls, err := ioutil.ReadDir(path)
	if (err != nil) && gDebugMode {
		log.Println("func isDoorway: can't read dir", path)
	}
	counter := 0
	for _, f := range ls {
		if f.IsDir() {
			counter++
		}
		if ext := filepath.Ext(f.Name()); ext == ".php" ||
			ext == ".htm" ||
			ext == ".html" {
			counter++
		}
	}
	if counter > gMaxPHPandHTML {
		return true
	}
	return false
}

///////////////////////////////////////////////////////////////////////////
func QCR_ScanDirectoriesFn(fPath string, info os.FileInfo, err error) error {
	name := info.Name()
	if name == "." {
		return nil
	}
	mode := info.Mode()

	if mode&os.ModeSymlink != 0 {
		gSymLinks = append(gSymLinks, fPath)
		return nil
	} else if !mode.IsRegular() && !mode.IsDir() {
		gUnixExec = append(gUnixExec, fPath)
		addResult(fPath, "other", " Unix non regular file")
		if gDebugMode {
			log.Println("Unix non regular file:", fPath, "matched")
		}
		return nil
	}

	if (name[0] == '.') &&
		(info.Name() != ".htaccess") &&
		(info.Name() != ".htpasswd") {
		gHiddenFiles = append(gHiddenFiles, fPath)
	}

	if mode.IsDir() {
		if gDebugMode {
			log.Println("Scan " + fPath)
		}

		if isDoorway(fPath) {
			gDoorway = append(gDoorway, fPath)
		}
		gFoundTotalDirs++
	} else {
		for _, i := range gIgnoredDir {
			if strings.Index(fPath, i) == 0 {
				return nil
			}
		}
		ext := getExt(fPath)

		needToScan := def.scanAllFiles
		if stringInArray(ext, gSensitiveFiles) {
			needToScan = true
			gUnixExec = append(gUnixExec, fPath)
		}
		// which files should be scanned
		if len(gIgnoredExt) > 0 {
			needToScan = needToScan && !stringInArray(ext, gIgnoredExt)
		}
		if !needToScan {
			return nil
		}

		gQueueToScan = append(gQueueToScan, fPath)
	}

	return nil
}

///////////////////////////////////////////////////////////////////////////
func getFragment(subj string, pos int) string {
	start := 0
	end := len(subj)
	if (pos > end) || (pos < start) {
		pos = (start + end) / 2
	}
	if e := (pos + gMaxPreviewLen); e < end {
		if e > 0 {
			end = e
		}
	}
	if s := (pos - 10); s > 0 {
		if s < end {
			start = s
		}
	}

	var lineNo string
	if n := strings.Count(subj[0:pos], "\n") + 1; n > 1 {
		lineNo = strconv.Itoa(n)
	} else {
		lineNo = "?"
	}

	res := "L" + lineNo + ": " + subj[start:pos] + "%%%>>>" + subj[pos:end-1]
	// must run func prepare(), or singleSpace will not work
	res = allToSpace.Replace(res)
	res = singleSpace.Replace(res)

	return res
}

///////////////////////////////////////////////////////////////////////////
func escapedHexToHex(subj string) string {
	ret := subj
	if len(subj) > 2 {
		str, err := strconv.ParseInt(subj[2:], 16, 64)
		if err == nil {
			ret = string(rune(str))
		}
	}
	return ret
}

func escapedOctDec(subj string) string {
	ret := subj
	if len(subj) > 1 {
		str, err := strconv.ParseInt(subj[1:], 8, 64)
		if err == nil {
			ret = string(rune(str))
		}
	}
	return ret
}

func chrIntVal(subj string) string {
	ret := subj
	if len(subj) > 4 {
		str, err := strconv.ParseInt(subj[4:], 0, 64)
		if err == nil {
			ret = string(rune(str))
		}
	}
	return ret
}

///////////////////////////////////////////////////////////////////////////
func QCR_SearchPHP(subj string) int {
	indexes := phpRegexp.FindIndex([]byte(subj), 0)
	if len(indexes) > 0 {
		return indexes[0]
	}

	indexes = phpScriptRegexp.FindIndex([]byte(subj), 0)
	if len(indexes) > 0 {
		return indexes[0]
	}

	return -1
}

///////////////////////////////////////////////////////////////////////////
func knownUrl(par_URL string) bool {
	par_URL = strings.ToLower(par_URL)
	for _, i := range gIgnoredUrl {
		if strings.Contains(par_URL, i) {
			return true
		}
	}
	return false
}

///////////////////////////////////////////////////////////////////////////
func checkVulnerability(filepath string, par_Content string) string {

	if stripos(filepath, "editor/filemanager/") {
		if stripos(filepath, "editor/filemanager/upload/test.html") ||
			stripos(filepath, "editor/filemanager/browser/default/connectors/php/") ||
			stripos(filepath, "editor/filemanager/connectors/uploadtest.html") ||
			stripos(filepath, "editor/filemanager/browser/default/connectors/test.html") {
			gVulnerable = append(gVulnerable, filepath)
			return "AFU : FCKEDITOR : http://www.exploit-db.com/exploits/17644/ & /exploit/249"
		}
	}

	if stripos(filepath, "inc_php/image_view.class.php") ||
		stripos(filepath, "/inc_php/framework/image_view.class.php") {
		if !strings.Contains(par_Content, "showImageByID") {
			gVulnerable = append(gVulnerable, filepath)
			return "AFU : REVSLIDER : http://www.exploit-db.com/exploits/35385/"
		}
		return ""
	}

	if stripos(filepath, "includes/database/database.inc") {
		if strings.Contains(par_Content, "foreach ($data as $i => value)") {
			gVulnerable = append(gVulnerable, filepath)
			return "SQLI : DRUPAL : CVE-2014-3704"
		}
		return ""
	}

	if stripos(filepath, "engine/classes/min/index.php") {
		if !stripos(par_Content, "tr_replace(chr(0)") {
			gVulnerable = append(gVulnerable, filepath)
			return "AFD : MINIFY : CVE-2013-6619"
		}
		return ""
	}

	if stripos(filepath, "timthumb.php") ||
		stripos(filepath, "thumb.php") ||
		stripos(filepath, "cache.php") ||
		stripos(filepath, "_img.php") {
		if strings.Contains(par_Content, "code.google.com/p/timthub") && !strings.Contains(par_Content, "2.8.14") {
			gVulnerable = append(gVulnerable, filepath)
			return "RCE : TIMTHUMB : CVE-2011-4106,CVE-2014-4663"
		}
		return ""
	}

	if stripos(filepath, "fancybox-for-wordpress/fancybox.php") {
		if strings.Contains(par_Content, "'reset' = $_REQUEST['action']") {
			gVulnerable = append(gVulnerable, filepath)
			return "CODE INJECTION : FANCYBOX"
		}
		return ""
	}

	if stripos(filepath, "tiny_mce/plugins/tinybrowser/tinybrowser.php") {
		gVulnerable = append(gVulnerable, filepath)
		return "AFU : TINYMCE : http://www.exploit-db.com/exploits/9296/"
	}

	if stripos(filepath, "scripts/setup.php") {
		if strings.Contains(par_Content, "PMA_Config") {
			gVulnerable = append(gVulnerable, filepath)
			return "CODE INJECTION : PHPMYADMIN : http://1337day.com/exploit/5334"
		}
		return ""
	}

	if stripos(filepath, "/uploadify.php") {
		if strings.Contains(par_Content, "move_uploaded_file($tempFile,$targetFile") {
			gVulnerable = append(gVulnerable, filepath)
			return "AFU : UPLOADIFY : CVE: 2012-1153"
		}
		return ""
	}

	return ""
}

///////////////////////////////////////////////////////////////////////////
// Working like php_strip_whitespace, but it's not the same
func phpStrip(s string) string {
	s = rComment1.ReplaceAllString(s, "", 0)
	s = strings.Replace(s, "\n", "", -1)
	s = strings.Replace(s, "<?php", "<?php ", 1)
	s = strings.Replace(s, "?>", " ?>", 1)
	s = rComment2.ReplaceAllString(s, "", 0)
	return s
}
func unwrapObfu(s string) string {
	s = strings.Replace(s, "@", "", -1)
	s = allToSpace.Replace(s)
	s = singleSpace.Replace(s)
	s = excessiveSpace.Replace(s)
	s = rChrItnVal.ReplaceAllStringFunc(s, chrIntVal)
	s = rEscHex.ReplaceAllStringFunc(s, escapedHexToHex)
	s = rEscDec.ReplaceAllStringFunc(s, escapedOctDec)
	return s
}

///////////////////////////////////////////////////////////////////////////
// append new SignedRegexp to db
// separate function is needed for fast regexp lib changing
func appendCompiledRegexp(r string, db []SignedRegexp) []SignedRegexp {
	return append(db, SignedRegexp{pcreCompile("(?smi)"+r, 0), r, myCheckSum(r)})
}

func prepare() {
	// this is dirty hack for unwrapObfu func
	s := " "
	for i := 9999; i > 1; i-- {
		s += " "
		tonnsOfSpaces = append(tonnsOfSpaces, s, " ")
	}
	singleSpace = strings.NewReplacer(tonnsOfSpaces...)

	for _, l := range g_SusDBRaw {
		gSusDB = appendCompiledRegexp(l, gSusDB)
	}
	for _, l := range g_FlexDBSheRaw {
		gFlexDBShe = appendCompiledRegexp(l, gFlexDBShe)
	}
	for _, l := range gX_FlexDBSheRaw {
		gX_FlexDBShe = appendCompiledRegexp(l, gX_FlexDBShe)
	}
	for _, l := range gXX_FlexDBSheRaw {
		gXX_FlexDBShe = appendCompiledRegexp(l, gXX_FlexDBShe)
	}
	for _, l := range g_ExceptFlexRaw {
		gExceptFlex = appendCompiledRegexp(l, gExceptFlex)
	}
	for _, l := range g_AdwareSigRaw {
		gAdwareSig = appendCompiledRegexp(l, gAdwareSig)
	}
	for _, l := range g_PhishingSigRaw {
		gPhishingSig = appendCompiledRegexp(l, gPhishingSig)
	}
	for _, l := range g_JSVirSigRaw {
		gJSVirSig = appendCompiledRegexp(l, gJSVirSig)
	}
	for _, l := range gX_JSVirSigRaw {
		gX_JSVirSig = appendCompiledRegexp(l, gX_JSVirSig)
	}
	// ahocorasick building
	for i, s := range g_DBSheRaw {
		g_DBSheRaw[i] = strings.ToLower(s)
	}
	for i, s := range gX_DBSheRaw {
		gX_DBSheRaw[i] = strings.ToLower(s)
	}
	gDBShe.Build(g_DBSheRaw)
	gX_DBShe.Build(gX_DBSheRaw)
}

///////////////////////////////////////////////////////////////////////////
func QCR_GoScan() {
	ti := time.Now().UnixNano()
	prepare()
	if gDebugMode {
		log.Println("Regexp db compiled", time.Duration(time.Now().UnixNano()-ti))
		log.Println("QCR_GoScan started")
		if len(gQueueToScan) == 0 {
			log.Fatalln("There is nothing to scan, scan queue == 0")
		}
	}

	if gAsyncMode {
		var wg sync.WaitGroup
		wg.Add(len(gQueueToScan))
		out := make(chan string, 1)
		fch := make(chan string, 1)
		t := time.Tick(111 * time.Millisecond)
		prog := ""
		progLast := ""
		done := false
		go func() {
			i := 0
			x := "--\\|/"
			for range t {
				s := ""
				for j := 0; j < len(progLast); j++ {
					s += " "
				}
				progLast = strings.Replace(prog, def.path, ".", 1)
				p := string(x[i%len(x)])
				i++
				if !done {
					fmt.Printf(s + "\r" + p + progLast)
				}
			}
		}()
		go func() {
			mess := " files scanned. Now scanning "
			for i := range gQueueToScan {
				prog = fmt.Sprintf(" %d / %d"+mess+"%q\r", i, len(gQueueToScan), <-out)
				wg.Done()
			}
		}()
		for _, f := range gQueueToScan {
			fch <- f
			for runtime.NumGoroutine() > (def.threads*30 + 9) {
				time.Sleep(100 * time.Millisecond)
			}
			go func() {
				out <- QCR_ScanFile(<-fch)
			}()
		}
		wg.Wait()
		done = true
	} else {
		for _, f := range gQueueToScan {
			QCR_ScanFile(f)
		}
	}
}

///////////////////////////////////////////////////////////////////////////`
func QCR_ScanFile(fPath string) string {

	stat, _ := os.Lstat(fPath)

	if gDebugMode {
		log.Println("Scan file " + fPath)
	}

	if def.maxSizeToScan > 0 && stat.Size() > int64(def.maxSizeToScan) {
		gBigFiles = append(gBigFiles, fPath)
		return fPath
	}

	//lStartFileScan := time.Now().UnixNano()
	var contentUnwrapped, content string

	if stat.Mode().IsRegular() {
		read, err := ioutil.ReadFile(fPath)
		for ; strings.Contains(fmt.Sprint(err), "too many open files"); read, err = ioutil.ReadFile(fPath) {
			r := time.Duration(rand.Intn(100))
			time.Sleep(r * time.Millisecond)
		}
		content = string(read)
		contentUnwrapped = unwrapObfu(phpStrip(content))
	}

	// unix executables
	if strings.Contains(content, string(byte(127))+"ELF") {
		gUnixExec = append(gUnixExec, fPath)
		addResult(fPath, "other", " Unix executable \\x7F ELF file")
		if gDebugMode {
			log.Println("Unix executable ELF:", fPath, "matched")
		}
		return fPath
	}

	if gKnownList[realCRC(content)+realCRC(stat.Name())] {
		return fPath
	}

	// check vulnerability in files
	var criticalDetected bool
	if vuln := checkVulnerability(fPath, content); vuln != "" {
		criticalDetected = true
		addResult(fPath, "crit", vuln)
		if gDebugMode {
			log.Println("Vulnerability detected:", fPath, "matched", vuln)
		}
	}

	// critical
	var sigID string
	gSkipNextCheck := false
	if pos := CriticalPHP(fPath, contentUnwrapped, &sigID); pos >= 0 {
		addResult(fPath, "crit", getFragment(contentUnwrapped, pos))
		gSkipNextCheck = true
	} else if pos := CriticalPHP(fPath, content, &sigID); pos >= 0 {
		addResult(fPath, "crit", getFragment(content, pos))
		gSkipNextCheck = true
	}

	if !gSkipNextCheck {
		heur := ""
		if heur = HeuristicChecker(content, fPath); heur != "" {
			criticalDetected = true
			addResult(fPath, "other", "Heuristcik checker "+heur)
		}
	}

	// critical JS
	if !gSkipNextCheck {
		if pos := CriticalJS(fPath, contentUnwrapped, &sigID); pos >= 0 {
			addResult(fPath, "js", getFragment(content, pos))
			addResult(fPath, "js", getFragment(content, pos))
			gSkipNextCheck = true
		}
	}

	// phishing
	if !gSkipNextCheck {
		if pos := Phishing(fPath, contentUnwrapped, &sigID); pos >= 0 {
			addResult(fPath, "crit", getFragment(content, pos))
			gSkipNextCheck = true
		}
	}

	if !gSkipNextCheck {
		if def.scanAllFiles || strings.Contains(fPath, "index.") {
			// check iframes
			if indexes := regexp.MustCompile("(?smi)<iframe[^>]+src.+?>").FindAllString(contentUnwrapped, -1); len(indexes) > 0 {
				for _, lstr := range indexes {
					if pos := regexp.MustCompile("((https?)|(ftp))://").FindIndex([]byte(lstr)); (len(pos) > 0) && (!knownUrl(lstr)) {
						addResult(fPath, "crit", getFragment(content, pos[0]))
						criticalDetected = true
					}
				}
			}

			// check empty links
			/*
				if indexes := regexp.MustCompile("(?smi)<a[^>]+href=([^>]+?)>(.*?)</a>").FindAllStringSubmatch(contentUnwrapped, -1); ((def.reportMask & gReportMaskSPAMLINKS) == gReportMaskSPAMLINKS) &&
					(len(indexes) > 0) {
					for _, matches := range indexes {
						if pos := regexp.MustCompile("((https?)|(ftp))://").FindString(matches[1]); (pos != "") &&
							(strings.TrimSpace(regexp.MustCompile("<[^>]*>").ReplaceAllString(matches[2], "")) == "") {

							needToAdd := true
							if (def.host != "" && stripos(matches[1], def.host)) || knownUrl(matches[1]) {
								needToAdd = false
							}
							if needToAdd && (len(gEmptyLink) < gMaxExtLinks) {
								gEmptyLink = append(gEmptyLink, i)
								if len(matches[0]) > gMaxPreviewLen {
									matches[0] = matches[0][0:gMaxPreviewLen]
								}
								addResult(fPath, "crit", "Spam check: "+matches[1])
								criticalDetected = true
							}
						}
					}
				}
			*/
		}

		// check for PHP code inside any type of file
		if !stripos(stat.Name(), ".ph") && !stripos(stat.Name(), ".htm") && !stripos(stat.Name(), ".tpl") {
			pos := QCR_SearchPHP(contentUnwrapped)
			if pos >= 0 {
				addResult(fPath, "crit", getFragment(content, pos))
				criticalDetected = true
			}
		}

		// htaccess
		if stat.Name() == ".htaccess" {
			for _, s := range []string{"auto_prepend_file", "auto_append_file", "^(%2d|-)[^=]+"} {
				if pos := strings.Index(content, s); (pos >= 0) && !criticalDetected {
					addResult(fPath, "crit", getFragment(content, pos))
					criticalDetected = true
				}
			}
			if !criticalDetected {
				if pos := regexp.MustCompile("(?smi)RewriteCond\\s+%\\{HTTP_HOST\\}/%1 \\!\\^\\[w\\.\\]\\*\\(\\[\\^/\\]\\+\\)/\\\\1\\$\\s+\\[NC\\]").FindStringIndex(content); len(pos) > 0 {
					addResult(fPath, "crit", getFragment(content, pos[0]))
					criticalDetected = true
				}
			}
			if !criticalDetected && (def.host != "") {
				lHTAContent := regexp.MustCompile("(?m)^\\s*#.+").ReplaceAllString(content, "")
				if indexes := regexp.MustCompile("(?smi)RewriteRule\\s+.+?\\s+http://(.+?)/.+\\s+\\[.*R=\\d+.*\\]").FindAllStringSubmatch(lHTAContent, -1); len(indexes) > 0 {
					for _, rule := range indexes {
						http := strings.Replace(rule[1], "www.", "", -1)
						if http != def.host {
							addResult(fPath, "crit", getFragment(rule[0], strings.Index(rule[0], rule[1])))
							criticalDetected = true
							continue
						}
					}
				}
			}
		}

		// warnings
		if pos := WarningPHP(fPath, contentUnwrapped, &sigID); pos > 0 {
			addResult(fPath, "crit", getFragment(content, pos))
			criticalDetected = true
		}

		// adware
		if pos := Adware(fPath, contentUnwrapped, &sigID); pos > 0 {
			addResult(fPath, "crit", getFragment(content, pos))
			criticalDetected = true
		}

	}
	// end of if (!gSkipNextCheck)

	return fPath
}

///////////////////////////////////////////////////////////////////////////
func addResult(file, threat, fragment string) {
	outputFormat := "%s\n\t%q\n"
	s := fmt.Sprintf(outputFormat, file, fragment)
	switch threat {
	case "crit":
		gTotalOutput.crit += s
	case "js":
		gTotalOutput.js += s
	case "other":
		gTotalOutput.crit += s
	default:
		if gDebugMode {
			log.Println("func addResult. Wrong threat type")
		}
	}
	gTotalOutput.all = append(gTotalOutput.all, file)
}

///////////////////////////////////////////////////////////////////////////
func WarningPHP(fPath, content string, sigID *string) int {
	if def.extraWarn {
		for _, item := range gSusDB {
			if pos := item.regexp.FindIndex([]byte(content), 0); pos != nil {
				if !checkException([]byte(content), pos[0]) {
					*sigID = item.sign
					return pos[0]
				}
			}
		}
	}

	if def.expertMode < 2 {
		if pos, _ := checkRegexpArray(gXX_FlexDBShe, content, sigID); pos >= 0 {
			return pos
		}
	}

	if def.expertMode < 1 {
		if pos, _ := checkRegexpArray(gX_FlexDBShe, content, sigID); pos >= 0 {
			return pos
		}
		contentLo := strings.ToLower(content)
		if m := gX_DBShe.Match(contentLo); len(m) > 0 {
			pos := strings.Index(contentLo, gX_DBSheRaw[m[0]])
			if !checkException([]byte(contentLo), pos) {
				*sigID = myCheckSum(gX_DBSheRaw[m[0]])
				return pos
			}
		}
	}
	return -1
}

///////////////////////////////////////////////////////////////////////////
func Adware(fPath, content string, sigID *string) int {
	if pos, _ := checkRegexpArray(gAdwareSig, content, sigID); pos >= 0 {
		return pos
	}
	return -1
}

///////////////////////////////////////////////////////////////////////////
func checkException(content []byte, pos int) bool {
	start := 0
	end := len(content)
	if e := (pos + 70); e < end {
		if e > 0 {
			end = e
		}
	}
	if s := (pos - 10); s > 0 {
		if s < end {
			start = s
		}
	}
	indexesStrPlus := content[start:end]

	for _, item := range gExceptFlex {
		if pos := item.regexp.FindIndex(indexesStrPlus, 0); pos != nil {
			return true
		}
	}
	return false
}

///////////////////////////////////////////////////////////////////////////
func Phishing(fPath string, content string, sigID *string) int {
	// need check file (by extension) ?
	if def.smartScan {
		ext := getExt(fPath)
		skipCheck := def.smartScan
		for _, e := range gPhishFiles {
			if ext == e {
				skipCheck = false
				break
			}
		}
		// need check file (by signatures) ?
		if skipCheck {
			if gPhishEntries.MatchString(content, 0) {
				skipCheck = false
			}
		}
		if skipCheck {
			if gDebugMode {
				log.Println("Skipped phs file", fPath, ", not critical.")
			}
			return -1
		}
	}

	if pos, r := checkRegexpArray(gPhishingSig, content, sigID); pos >= 0 {
		if gDebugMode {
			log.Println("Phishing:", fPath, "matched [", r, "] in", pos)
		}
		return pos
	}

	return -1
}

///////////////////////////////////////////////////////////////////////////
func CriticalJS(fPath string, content string, sigID *string) int {
	if def.smartScan {
		// need check file (by extension) ?
		skipCheck := def.smartScan
		ext := getExt(fPath)
		for _, e := range gVirusFiles {
			if ext == e {
				skipCheck = false
				break
			}
		}
		// need check file (by signatures) ?
		if skipCheck {
			if gVirusEntries.MatchString(content, 0) {
				skipCheck = false
			}
		}
		if skipCheck {
			if gDebugMode {
				log.Println("Skipped js file", fPath, ", not critical.")
			}
			return -1
		}
	}

	if def.expertMode > 1 {
		if pos, r := checkRegexpArray(gX_JSVirSig, content, sigID); pos >= 0 {
			if gDebugMode {
				log.Println("JS:", fPath, "matched [", r, "] in", pos)
			}
			return pos
		}
	} else {
		if pos, r := checkRegexpArray(gJSVirSig, content, sigID); pos >= 0 {
			if gDebugMode {
				log.Println("JS:", fPath, "matched [", r, "] in", pos)
			}
			return pos
		}
	}
	return -1
}

///////////////////////////////////////////////////////////////////////////
func HeuristicChecker(content, fPath string) string {
	stat, _ := os.Lstat(fPath)
	t, _ := times.Stat(fPath)
	// most likely changed by touch
	if times.HasChangeTime && t.ChangeTime().Unix() < t.ModTime().Unix() {
		return "Suspicious file mtime and ctime"
	}

	p := int(stat.Mode().Perm())
	if p&0400 != 0400 ||
		p == 0404 ||
		p == 0505 {
		return "Suspicious file permissions"
	}

	if strings.Contains(stat.Name(), ".ph") && (strings.Contains(fPath, "/images/stories/") ||

		strings.Contains(fPath, "/wp-content/uplad/")) {
		return "Suspicious file location"
	}

	return ""
}

///////////////////////////////////////////////////////////////////////////
func CriticalPHP(fPath string, content string, sigID *string) int {
	stat, _ := os.Lstat(fPath)

	skipCheck := def.smartScan
	if def.smartScan {
		// need check file (by extension) ?
		ext := getExt(fPath)
		for _, e := range gCriticalFiles {
			if ext == e {
				skipCheck = false
				break
			}
		}
		// need check file (by signatures) ?
		if skipCheck {
			if gCriticalEntries.MatchString(content, 0) {
				skipCheck = false
			}
		}
		if skipCheck {
			if gDebugMode {
				log.Println("Skipped js file", fPath, ", not critical.")
			}
			return -1
		}
	}

	// if not critical - skip
	if skipCheck {
		if gDebugMode {
			log.Println("Skipped file", fPath, ", not critical.")
		}
		return -1
	}

	if def.expertMode > 1 {
		if pos, r := checkRegexpArray(gXX_FlexDBShe, content, sigID); pos >= 0 {
			if gDebugMode {
				log.Println("CRIT 2:", fPath, "matched [", r, "] in", pos)
			}
			return pos
		}
	} else if def.expertMode > 0 {
		if pos, r := checkRegexpArray(gX_FlexDBShe, content, sigID); pos >= 0 {
			if gDebugMode {
				log.Println("CRIT 2:", fPath, "matched [", r, "] in", pos)
			}
			return pos
		}
	} else {
		if pos, r := checkRegexpArray(gFlexDBShe, content, sigID); pos >= 0 {
			if gDebugMode {
				log.Println("CRIT 1:", fPath, "matched [", r, "] in", pos)
			}
			return pos
		}
	}

	contentLo := strings.ToLower(content)

	if m := gDBShe.Match(contentLo); len(m) > 0 {
		item := g_DBSheRaw[m[0]]
		pos := strings.Index(contentLo, item)
		if !checkException([]byte(contentLo), pos) {
			*sigID = myCheckSum(item)
			if gDebugMode {
				log.Println("CRIT 4:", fPath, "matched [", item, "] in", pos)
			}
			return pos
		}
	}

	if def.expertMode > 0 {
		if m := gX_DBShe.Match(contentLo); len(m) > 0 {
			item := gX_DBSheRaw[m[0]]
			pos := strings.Index(contentLo, item)
			if !checkException([]byte(contentLo), pos) {
				*sigID = myCheckSum(item)
				if gDebugMode {
					log.Println("CRIT 4:", fPath, "matched [", item, "] in", pos)
				}
				return pos
			}
		}

		if strings.Contains(stat.Name(), ".ph") && (def.expertMode > 1) {
			gSpecials := []string{");#"}
			for _, item := range gSpecials {
				if stripos(content, item) {
					pos := strings.Index(content, item)
					*sigID = myCheckSum(item)
					return pos
				}
			}
		}
	}

	if (strings.Index(content, "GIF89") == 0) && strings.Contains(fPath, ".php") {
		pos := 0
		if gDebugMode {
			log.Println("CRIT :", fPath, "matched [GIF89] in", pos)
		}
		return pos
	}

	// detect uploaders / droppers
	if def.expertMode > 1 {
		indexes := rCopy.FindIndex([]byte(content), 0)
		pos := -1
		switch {
		case len(indexes) > 0:
			pos = indexes[0]
		case strings.Contains(content, "multipart/form-data"):
			pos = strings.Index(content, "multipart/form-data")
		case strings.Contains(content, "$_FILE["):
			pos = strings.Index(content, "$_FILE[")
		case strings.Contains(content, "move_uploaded_file"):
			pos = strings.Index(content, "move_uploaded_file")
		}
		if (stat.Size() < 1024) &&
			strings.Contains(stat.Name(), ".ph") &&
			(pos >= 0) {
			if gDebugMode {
				log.Println("CRIT 7:", fPath, "matched [", content[pos:][:5], "] in", pos)
			}
			return pos
		}
	}

	// count number of base64_decode entries
	if count := strings.Count(content, "base64_decode"); count > 10 {
		gBase64 = append(gBase64, fPath)
		if gDebugMode {
			log.Println("CRIT 10:", fPath, "matched")
		}
	}

	return -1
}

///////////////////////////////////////////////////////////////////////////
func getReport() (report string) {

	report += "# ZHIVAGO Website Malware Scanner v" + gZhivagoVersion + "\n"
	report += "# https://revisium.com/zhivago/\n\n"

	report += "# You may want to send this report to ai@revisium.com for further free malware analysis\n\n"

	if gTotalOutput.crit != "" {
		report += gColorRed + "Critical threats" + gColorOff + "\n"
		report += strings.Replace(gTotalOutput.crit, "%%%>>>", gColorRed+"%>"+gColorOff, -1)
	}
	if gTotalOutput.js != "" {
		report += gColorRed + "\nJS threats" + gColorOff + "\n"
		report += strings.Replace(gTotalOutput.js, "%%%>>>", gColorRed+"%>"+gColorOff, -1)
	}
	if gTotalOutput.other != "" {
		report += gColorRed + "\nOther threats" + gColorOff + "\n"
		report += strings.Replace(gTotalOutput.other, "%%%>>>", gColorRed+"%>"+gColorOff, -1)
	}
	if len(gBase64) != 0 {
		report += fmt.Sprintln("\nBase64:\n" + strings.Join(gBase64, "\n"))
	}
	if len(gDoorway) != 0 {
		report += fmt.Sprintln("\nDoorway:\n" + strings.Join(gDoorway, "\n"))
	}
	if len(gSymLinks) != 0 {
		report += fmt.Sprintln("\nSymLinks\n" + strings.Join(gSymLinks, "\n"))
	}
	//if len(gUnixExec) != 0 { report += fmt.Sprintln("UnixExec", strings.Join(gUnixExec, "\n"))) }
	if len(gHiddenFiles) != 0 {
		report += fmt.Sprintln("\nHiddenFiles\n" + strings.Join(gHiddenFiles, "\n"))
	}
	if len(gBigFiles) != 0 {
		report += fmt.Sprintln("\nBigFiles\n" + strings.Join(gBigFiles, "\n"))
	}
	if report == "" {
		report = "\nEverithing seems to be OK\n"
	}
	return
}

///////////////////////////////////////////////////////////////////////////
func main() {

	// additional garbage collection every 5 seconds
	gcT := time.Tick(5 * time.Second)
	go func() {
		for range gcT {
			runtime.GC()
		}
	}()

	// get random seed for random func
	rand.Seed(time.Now().UnixNano())

	// Don't use options until flags.Parse() func, they are defaults until parsed
	// Flags Options
	var optHelp bool
	flag.BoolVar(&optHelp, "h", false, "print help message")
	flag.BoolVar(&optHelp, "help", false, "")
	var optOneFile string
	flag.StringVar(&optOneFile, "j", "", "Full path to single file to check")
	flag.StringVar(&optOneFile, "file", "", "")
	flag.IntVar(&def.threads, "t", def.threads, "The number of threads")
	flag.IntVar(&def.threads, "threads", def.threads, "now it is half of your core's number:"+fmt.Sprint(runtime.NumCPU()-1))
	flag.StringVar(&def.path, "p", def.path, "Directory path to scan, by default the file directory is used")
	flag.StringVar(&def.path, "path", def.path, "Current path: "+def.path)
	flag.StringVar(&def.host, "host", def.path, "Set host, to enable some additional checks")
	var optSize string
	flag.StringVar(&optSize, "s", "600k", "Scan files are smaller than SIZE. 0 - All files.")
	flag.StringVar(&optSize, "size", "600k", "Current value: "+fmt.Sprint(def.maxSizeToScan))
	var optCms string
	flag.StringVar(&optCms, "e", "", "cms filename to load .aknown files from.")
	flag.StringVar(&optCms, "cms", "", "E.g. -cms=wordpress")
	flag.BoolVar(&def.extraWarn, "x", def.extraWarn, "Set scan mode. 0 - for basic, 1 - for expert and 2 for paranoic.")
	flag.BoolVar(&def.extraWarn, "extra", def.extraWarn, "")
	flag.IntVar(&def.expertMode, "m", def.expertMode, "Set scan mode. 0 - for basic, 1 - for expert and 2 for paranoic.")
	flag.IntVar(&def.expertMode, "mode", def.expertMode, "")
	var optPHPOnly bool
	flag.BoolVar(&optPHPOnly, "php-only", false, "Scan only php, html and js files")
	var optSensitive bool
	flag.BoolVar(&optPHPOnly, "sens", false, "Scan only sensitive files php, htm, tpl, htaccess, sh, etc...")
	flag.StringVar(&def.skipExt, "k", def.skipExt, "Skip specific extensions. E.g. -skip=jpg,gif,png,xls,pdf")
	flag.StringVar(&def.skipExt, "skip", def.skipExt, "")
	flag.StringVar(&def.reportPath, "r", def.reportPath, "Path ot save report file. E.g. -path=/var/www")
	flag.StringVar(&def.reportPath, "report", def.reportPath, "")
	//var optCmd string
	//flag.StringVar(&optCmd, "cmd", "", "Run command after scanning")
	//var optQuarantine bool
	//flag.BoolVar(&optQuarantine, "quarantine", false, "Archive all malware from report")
	var optWith2check bool
	flag.BoolVar(&optWith2check, "with-2check", false, "Create or use ZHIVAGO-DOUBLECHECK file")
	// var def.smartScan bool // already set in var()
	flag.BoolVar(&def.smartScan, "smart-scan", def.smartScan, "Use smart scan mode to optimize check")

	// Flags Options
	// Here options are defaults
	flag.Parse()
	// Now, options are parsed and you can use them
	if gDebugMode {
		log.SetFlags(log.Ltime | log.Lmicroseconds | log.Lshortfile)
	} else {
		log.SetFlags(log.Ltime | log.Lmicroseconds)
	}

	fmt.Println("ZHIVAGO - Website Malware Scanner v" + gZhivagoVersion)
	fmt.Println("----------------------------------------------------")

	if optHelp {
		fmt.Println(`
		Usage: ./zhivago [OPTIONS]
		Current default path is:`, def.path, `

		-j, -file=FILE         Full path to single file to check
		-p, -path=PATH         Directory path to scan, by default the file directory is used Current path:`, def.path, `

		-s, -size=SIZE         Scan files are smaller than SIZE. 0 - All files. Current value:`, def.maxSizeToScan, `bytes
		-t, -threads=INT       The number of threads, now it is half of your core's number:`, fmt.Sprint(runtime.NumCPU()-1), `
		                       Also, max number of simultaneously opened files ~ threads * 30

		-e, -cms=FILE          cms filename to load .aknown files from. E.g. -cms=wordpress
		-host=site.ru          Set host, to enable some additional checks

		-m, -mode=INT          Set scan mode. 0 - for basic, 1 - for expert and 2 for paranoic.
		-x, -extra             Add additional warnings, a lot of false-positive detections

		-php-only              Scan only php, html and js files
		-sens                  Scan only sensitive files php, htm, tpl, htaccess, sh, etc...
		-smart-scan        Smart scan                                   // experimental

		-k, -skip            Skip specific extensions. E.g. -skip=jpg,gif,png,xls,pdf
		-with-2check         Create or use ZHIVAGO-DOUBLECHECK file   // partialy ready
		-r, -report          Path ot save report file. E.g. -path=/var/www

		-help              Display this help and exit`)
		os.Exit(0)
	}

	// Init
	mainStartTime := time.Now().UnixNano()

	runtime.GOMAXPROCS(def.threads)
	/*var rLimit syscall.Rlimit
	rLimit.Max = uint64(def.threads) * 9
	rLimit.Cur = uint64(def.threads) * 9
	err := syscall.Setrlimit(syscall.RLIMIT_NOFILE, &rLimit)
	if err != nil {
		log.Println("Error Setting Rlimit ", err)
	}
	err = syscall.Getrlimit(syscall.RLIMIT_NOFILE, &rLimit)
	if err != nil {
		log.Println("Error Getting Rlimit ", err)
	}*/

	if optSensitive {
		def.scanAllFiles = false
	}
	if optPHPOnly {
		gSensitiveFiles = []string{"php", "htm", "html", "js"}
		def.scanAllFiles = false
	}
	fmt.Println(def.expertMode, "level of check enabled")
	if def.expertMode == 0 {
		fmt.Println("Scanning has been done in simple mode. It is strongly recommended to perform scanning in \"Expert\" mode. See readme.txt for details.")
	}

	def.maxSizeToScan = getBytes(optSize)

	def.skipExt = strings.ToLower(strings.TrimSpace(def.skipExt))
	if def.skipExt != "" {
		skipExt := regexp.MustCompile("[,;]").Split(def.skipExt, -1)
		for _, ext := range skipExt {
			gIgnoredExt = append(gIgnoredExt, strings.TrimSpace(ext))
		}
		fmt.Println("Skip extensions: ", gIgnoredExt)
	}

	if def.path == "" {
		log.Fatalln("Path to scanning directory is empty!")
	} else if _, err := os.Stat(def.path); err != nil {
		log.Fatalln("Cannot stat directory '"+def.path+"'!\n", err)
	} else if err := os.Chdir(def.path); err != nil {
		log.Fatalln("Can't change directory to '"+def.path+"'\n", err)
	}

	fileIgnoreFile := def.path + gPathSep + ".aignore"
	dirIgnoreFile := def.path + gPathSep + ".adirignore"
	urlIgnoreFile := def.path + gPathSep + ".aurlignore"
	knownFileName := def.path + gPathSep + ".aknown"

	if _, e := os.Stat(fileIgnoreFile); e == nil {
		f_bytes, _ := ioutil.ReadFile(fileIgnoreFile)
		f := strings.Split(string(f_bytes), "\n")
		for _, line := range f {
			gIgnoredFiles = append(gIgnoredFiles, strings.Split(strings.TrimSpace(line), "\t")...)
		}
	}

	if _, e := os.Stat(dirIgnoreFile); e == nil {
		f_bytes, _ := ioutil.ReadFile(dirIgnoreFile)
		f := strings.Split(string(f_bytes), "\n")
		for _, line := range f {
			if fileExists(line) {
				gIgnoredDir = append(gIgnoredDir, realpath(line))
			}
		}
	}

	if _, e := os.Lstat(urlIgnoreFile); e == nil {
		f_bytes, _ := ioutil.ReadFile(urlIgnoreFile)
		f := strings.Split(string(f_bytes), "\n")
		for _, line := range f {
			gIgnoredUrl = append(gIgnoredUrl, strings.TrimSpace(line))
		}
	}

	knownFilesFolder := def.path + gPathSep + "known_files"
	knownFilesDirs := []string{"."}

	if files, _ := ioutil.ReadDir(knownFilesFolder); len(files) > 0 {
		for _, fInfo := range files {
			if (fInfo.Name() == ".") || (fInfo.Name() == "..") {
				continue
			}
			if optCms != "" && fInfo.Name() == optCms {
				knownFilesDirs = append(knownFilesDirs, knownFilesFolder+gPathSep+fInfo.Name())
			}
		}
	}

	for _, path := range knownFilesDirs {
		if files, _ := ioutil.ReadDir(path); len(files) > 0 {
			for _, fInfo := range files {
				if fInfo.Name() == "." || fInfo.Name() == ".." {
					continue
				}
				if strings.Contains(fInfo.Name(), knownFileName) {
					fmt.Println("Loading", fInfo)
					b, _ := ioutil.ReadFile(path + gPathSep + fInfo.Name())
					f := string(b)
					for _, line := range strings.Split(f, "\n") {
						i, err := strconv.Atoi(line)
						if err == nil {
							gKnownList[i] = true
						}
					}
				}
			}
		}
	}

	if def.reportPath == "" {
		def.reportPath = "."
	}

	if err := writable(def.reportPath); err != nil {
		log.Fatalln("Cannot write report to directory '"+def.reportPath+"'!\n", err)
	}

	fmt.Printf("Loaded %d known files\n", len(gKnownList))

	if optOneFile != "" {
		fmt.Println(QCR_ScanFile(optOneFile))
		report := getReport()
		fmt.Println(report)
		return
	}

	CmsDetector := CmsVersionDetector{".", []string{}, []string{}}
	CmsDetector.detect()
	for i, cms := range CmsDetector.types {
		fmt.Printf("Found CMS %v version %v\n", cms, CmsDetector.versions[i])
	}

	if fileExists(DoubleCheckFile) && optWith2check {
		// scan list of files from file
		fmt.Println("Start scanning the list from", DoubleCheckFile)
		f_bytes, _ := ioutil.ReadFile(DoubleCheckFile)
		f := strings.Split(string(f_bytes), "\n")
		// remove 1st string with <?php die("Forbidden"); ?>
		f = f[1:]
		for _, l := range f {
			l = filepath.Clean(l)
			if fileExists(l) {
				gQueueToScan = append(gQueueToScan, l)
			}
		}
		fmt.Printf("Compiled queue to check: %d files in %d folders\n", len(gQueueToScan), gFoundTotalDirs)
	} else {
		err := filepath.Walk(def.path, QCR_ScanDirectoriesFn)
		if err != nil {
			log.Println("Can't scan directory Error:", err)
		}
	}
	fmt.Printf("Compiled queue to check: %d files\n", len(gQueueToScan))

	fmt.Println("Start scanning", def.path)
	QCR_GoScan()
	fmt.Println()
	fmt.Println("Scanning complete! Time taken", time.Duration(time.Now().UnixNano()-mainStartTime))
	fmt.Println()

	// print report
	report := getReport()
	fmt.Println(report)

	fmt.Printf("Time taken %v\n", time.Duration(time.Now().UnixNano()-mainStartTime))
	// write report
	date := time.Now().Format("2006.01.02-150405")
	report = strings.Replace(report, gColorOff, "", -1)
	report = strings.Replace(report, gColorRed, "", -1)
	def.reportPath = filepath.Clean(def.reportPath + gPathSep + fmt.Sprintf("ZHIVAGO-REPORT-%s-%d.txt", date, rand.Intn(1000000)))
	f, err := os.Create(def.reportPath)
	if err != nil {
		log.Fatalln("Cannot write to '"+def.reportPath+"'!\n", err)
	}
	defer f.Close()
	if b, err := f.Write([]byte(report)); err != nil {
		fmt.Println("Can't write report to", def.reportPath)
	} else {
		fmt.Println("Written", b, "bytes into report file", def.reportPath)
	}

	if optWith2check && (len(gTotalOutput.all) > 0) {
		if !fileExists(DoubleCheckFile) {
			if err := ioutil.WriteFile(DoubleCheckFile, []byte("# ZHIVAGO Malware Scanner Doublecheck File\n"), 0664); err == nil {
				all := gTotalOutput.all

				//delete duplicates
				found := make(map[string]bool)
				l := 0
				for i, x := range all {
					if !found[x] {
						found[x] = true
						all[l] = all[i]
						l++
					}
				}
				all = all[:l]
				//all = array_values(array_unique(tmpIndex));
				w := "# ZHIVAGO Malware Scanner Doublecheck File"
				for _, l := range all {
					w += "\n" + strings.Replace(l, def.path, ".", 1)
				}
				if err := ioutil.WriteFile(DoubleCheckFile, []byte(w), 0440); err != nil {
					log.Println("Cant write to", DoubleCheckFile)
				} else {
					fmt.Printf("Wrote %d bytes to %s\n", len(w), DoubleCheckFile)
				}
			} else {
				log.Println("Error! Cannot create " + DoubleCheckFile)
			}
		} else {
			fmt.Println(DoubleCheckFile + " already exists.")
		}

	}
}
