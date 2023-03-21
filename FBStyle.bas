''------------------------------------------------------------------------------
''
'' File    : fbstyle.bas - FreeBASIC Beautifier Program
''
'' FBSTYLE.EXE is a conversion of BCB.EXE to FreeBASIC so that it can be used on
'' the linux platform. Origional program written by Garvan O'Keeffe, Mike Henning
'' and Vic McLung
''
'' BCB.EXE - BC Beautifier, this is a merger of Garvan's ChangeCase.bas and
'' Mike's FreeBASICIndent, with a few changes to handle more toggle directives and updates.
''
'' Purpose : Changes the case of keywords/Indents a FreeBASIC source file.
''
'' Syntax  : BCB filename[.bas] [CCASE] [TABS]
'' CCASE   : 0 = ALL CAPS, 1 = Mixed, 2 = lower (default = 0)
'' TABS    : Number of spaced of indent (default = 1 tab)
''
'' History : Date       Reason
''           29-01-05   Created by Garvan O'Keeffe (GOK)
''           30-01-05   Modified by Vic McClung to handle additional toggle $directives (Vic)
''           31-01-05   Merged with Mike Henning's FreeBASICIndent.bas to create bcb.bas (Vic)
''           05-02-05   Incorporated Mike's changes and removed $PP as toggle (Vic)
''           09-02-05   Fixed TRIM(LCASE) bug. (GOK)
''           10-02-05   Fixed CONST bug (GOK)
''           20-05-05   Modified copy for FreeBASIC source code (GOK)
''           24-06-05   Ported to FreeBASIC for use on linux (GOK)
''           14-07-05   removed all toggle $directives (GOK)
''                      added asm block handling (GOK)
''                      removed special case CONST handling (GOK)
''           20-08-05   New FreeBASIC module level code handler (GOK)
''           01-12-05   Added casts to make it 0.15b compatible
''
''------------------------------------------------------------------------------
'' NOTES ON INTENDED BEHAVIOUR/COMPROMISES
''
'' REM is always justified full left if it is the first keyword on a line
'' Single quote is indented inline with code unless it is the first character of a line 
''     in which case it is justified left (i.e. left unchanged)
'' Multiline MACROS are left left unformated
''------------------------------------------------------------------------------
option explicit
const FALSE = 0
const TRUE = not FALSE
#define MAX(A,B) iif(A>B,A,B)

#include once "crt.bi"

declare function CC(byref s as string) as string
declare function IsKeyword(byval anyKeywords as zstring ptr, byval cKeywords as integer, _
		byref pszText as string, byval cchText as integer) as integer
declare function AdjustIndent()
declare function EndinLine()
declare sub FastParse(byref Arg as string)
declare function MCASE(byref s as string) as string
declare function STRNICMP (byref str1 as string, byref str2 as string, byval count as integer) as integer

const tok_end = 0  '' numbering follows order of tokens in BumpDowns
dim shared BumpDowns(7) as zstring * 15 => { _
		"end","endif","wend","loop","next","#endif", "glend", "glpopmatrix" }

dim shared BumpOuts(4) as zstring * 15 => { _
		"else","elseif","#elseif","#else","case" }

'' The enum must have same order of BumpUps and must be zero based
enum tok_BumpUps
	tok_if = 0 , tok_union ,tok_type, tok_function, tok_sub, tok_private, tok_public, tok_do, tok_while, tok_for
	tok_begin, tok_select, tok_with, tok_enum, tok__if, tok_glbegin, tok_glpushmatrix
	tok__ifdef, tok___ifndef, tok_asm, tok_scope
end enum

dim shared BumpUps(20) as zstring * 15 => { _
		"if","union","type","function","sub","private","public","do","while","for", _
		"begin","select","with","enum","#if" , "glbegin", "glpushmatrix", _
		"#ifdef", "#ifndef", "asm", "scope" }

dim shared as string Src
dim shared Stk(256) as zstring * 1024

dim shared as integer CCASE = 2
dim shared as integer indents = 1
dim shared as integer curlevel
dim shared as integer Ndx
dim shared as integer FP1, FP2

'' This list must be sorted ascending
#include "fb_keywords.inc"


''-------------------------------------------------------------------------------
''
'' FUNCTION : main()
''
'' Purpose  : Entry point
''
'' History  : Date       Reason
''            29-01-05   Created
''
''-------------------------------------------------------------------------------
	dim as string filein, fileout
	dim as string BSrc
	dim as string TempString
	dim as string id
	dim level(100) as integer
	dim as integer levelindex
	dim as byte ptr p, p1

	dim as integer DQ_ON, SQ_ON, LC_ON, ASM_ON, PP_ON, MACRO_ON, NELSE_ON, NELSE_STATE
	dim as integer SP_TAB = 9    '' Default to TAB
	dim as integer i

	if command = "" then
		print
		print "Syntax  : FBStyle filename[.bas] [CCASE] [INDENT]"
		print "CCASE   : 0 = ALL CAPS, 1 = Mixed, 2 = lower (default = 2)"
		print "INDENT  : = Number of spaces to Indent (default = 1 TAB)"
		print "            (Any number is interpreted as a space)"
		end 1              '' set to 1 to indicate error
	end if

	filein = command(1)

	if command(2) <> "" then
		CCASE = val(command(2))
	end if

	if command(3) <> "" then
		indents = val(command(3))
		SP_TAB = 32
	end if

	if lcase(right(filein,4)) <> ".bas" and _
			lcase(right(filein,4)) <> ".inc" and _
			lcase(right(filein,3)) <> ".bi" then filein = filein + ".bas"

	if dir(filein) = "" then
		print "File not found: " + filein, " FBStyle"
		end 1
	end if

	print "Processing...", filein

	fileout = filein + "xxx"

	FP1 = freefile
	if (open(filein,  for input, as FP1)) <> 0 then print "Error Opening file " + filein : end
	FP2 = freefile
	if (open(fileout, for output, as FP2)) <> 0 then print "Error Opening temp file " + fileout : end

  
	while not eof(FP1)
		line input #FP1, Src

		'' Strip tabs from left - careful of blank lines where p is null
		p = 0
		p = strptr(Src)
		if p <> 0 then
			while *p
				if *p > 32 then exit while
				if *p = 9 then *p = 32
				p += 1
			wend
		end if

		'' blank
		TempString = trim(Src)

		if TempString = "" then
			print #FP2, Src
			continue while
		end if

		DQ_ON = FALSE
		SQ_ON = FALSE
		BSrc = Src

		if lcase(left(trim(Src),4) ) = "rem " then
			i = instr(lcase(Src),"rem ")
			if i then mid(Src,i) = CC("rem ")
			print #FP2, ltrim(Src)
			continue while
		end if

		if lcase(trim(Src)) = "rem" then
			print #FP2, CC("rem")
			continue while
		end if

		if lcase(left(Src,1) ) = "'" then
			print #FP2, Src
			continue while
		end if
  
		FastParse(lcase(TempString))

		if Stk(1) = "#define" and Stk(Ndx) = "_" then
			MACRO_ON = TRUE
		end if

		if MACRO_ON then
			if Stk(Ndx) <> "_" then MACRO_ON = FALSE
			print #FP2, Src
			continue while
		end if


		id = string(AdjustIndent(),SP_TAB)

		if LC_ON then id = id + string(indents, SP_TAB)
		if Stk(Ndx) = "_" then
			LC_ON = TRUE
		else
			LC_ON = FALSE
		end if

		'' ASM blocks
		if Stk(1) = "asm" and Ndx = 1 then ASM_ON = TRUE
		if Stk(1) = "end" and Stk(2) = "asm" then  ASM_ON = FALSE
		if ASM_ON then print #FP2, id; trim(Src) : continue while

		'' Strip comments and strings from copy of source line
		p = strptr(BSrc)

		while *p
			if *p = 34 then DQ_ON = not DQ_ON : p = p+1 : continue while
			if DQ_ON then *p = 32
			if *p = 39 then SQ_ON = TRUE
			if SQ_ON then *p = 32
			p= p +1
		wend
		if instr(lcase(BSrc), " rem ") then BSrc = left(BSrc,instr(lcase(BSrc), " rem "))

		p = strptr(BSrc)
 
		'' Extract tokens that look like keywords
		while *p
			'' Is not alpha_
			while not ((*p > 64 and *p < 91) or (*p > 96 and *p < 123) or *p = 95)
				p = p + 1
				if *p = 0 then exit while
			wend
			'' is alpha_9
			p1 = p
			do
				while (*p > 64 and *p < 91) or (*p > 96 and *p < 123) or *p = 95
					p = p + 1
					if *p = 0 then exit while
				wend
				p = p + 1
			loop while p1 <> (p-1) and (*(p-1) > 47 and *(p-1) < 58)
			p-=1
			'' When a token is found check to see if it a keyword
			if p1 <> p then
				if IsKeyword(@GetKeyWord(0), ubound(GetKeyWord)+1, mid(BSrc,p1-cptr(byte ptr,strptr(BSrc))+1), p-p1) then
					mid(Src,p1-cptr(byte ptr,strptr(BSrc))+1) = CC(mid(BSrc, p1-cptr(byte ptr,strptr(BSrc))+1,p-p1))
				end if
			end if
		wend
		print #FP2, id; trim(Src)
	wend

	close FP1
	close FP2

	kill filein
	name fileout, filein
	print "Finished"
	end


''-------------------------------------------------------------------------------
''
'' FUNCTION    : CC(s)
''
'' Purpose     : Converts case of argument as specified in GLOBAL INT CCASE
''
'' History     : Date       Reason
''               29-01-05   Created
''
''-------------------------------------------------------------------------------
function CC(byref s as string) as string
	dim ls as string
	select case CCASE
	case 0 : ls = ucase(s)
	case 1 : ls = MCASE(s)
	case 2 : ls = lcase(s)
	case else : ls = ucase(s)
	end select
	return ls
end function


''-------------------------------------------------------------------------------
''
'' FUNCTION    : IsKeyword(s)
''
'' Purpose     : Binary search of array for keyword match
''
'' History     : Date       Reason
''               29-01-05   Modified from PellesC Sample code
''
''-------------------------------------------------------------------------------
function IsKeyword(byval anyKeywords as zstring ptr, byval cKeywords as integer, _
		byref pszText as string, byval cchText as integer) as integer

	dim as integer lo = 0
	dim as integer hi = cKeywords - 1

	'' binary search
	while hi >= lo
		dim tthis as integer
		tthis = (lo + hi) / 2
		dim cond as integer          '' case insensitive

		cond = strnicmp(anyKeywords[tthis*15], pszText, cchText)
		if cond > 0 then
			hi = tthis - 1
		elseif cond < 0 then
			lo = tthis + 1
		elseif anyKeywords[tthis*15+cchText] = 0 then
			return TRUE
		elseif IsKeyword(@anyKeywords[lo*15], tthis - lo, pszText, cchText) then
			return TRUE
		elseif IsKeyword(@anyKeywords[(tthis + 1)*15], hi - tthis, pszText, cchText) then
			return TRUE
		else
			exit while
		end if
	wend

	return FALSE
end function


''-------------------------------------------------------------------------------
''
'' FUNCTION    : AdjustIndent()
''
'' Purpose     : Calculates the correct indent level
''
'' History     : Date       Reason
''               31-01-05   Created
''
''-------------------------------------------------------------------------------
function AdjustIndent()
	dim as integer i
	dim as string t1
	static IntypeFlag

	'' If we get a single line comment the parser will just return
	'' immediatly with a zero Ndx, so will do nothing here.
	if Ndx = 0 then return curlevel

	for i = 0 to ubound(BumpUps)
		if BumpUps(i) = Stk(1) then
			if i=tok_function or i=tok_sub or i=tok_private or i=tok_public then
				if IntypeFlag or Stk(2) = "=" then
					return curlevel
				else
					curlevel = 0
				end if
			end if
			if EndinLine() then return curlevel
			if curlevel = indents and IntypeFlag =0 and (i = tok_union or i = tok_type or i = tok_enum) then curlevel = 0			
			if i = tok_union or i = tok_type or i = tok_asm then IntypeFlag += 1
			curlevel += indents
			return curlevel - indents
		end if
	next

	for i = 0 to ubound(BumpOuts)
		if BumpOuts(i) = Stk(1) then
			return MAX(0,curlevel - indents)
		end if
	next

	for i = 0 to ubound(BumpDowns)
		if BumpDowns(i) = Stk(1) then
			if i = tok_end then
				if Ndx = 1 then return curlevel
				if instr("0123456789", left(Stk(2), 1)) <> 0 then return curlevel
			end if
			curlevel = MAX(0,curlevel - indents)
			if IntypeFlag then IntypeFlag -=1
			return curlevel
		end if
	next

	if EndinLine() then
		curlevel = MAX(0,curlevel - indents)
		if IntypeFlag then IntypeFlag -=1
		return curlevel + indents
	end if

	t1 = " " + Stk(1) + " "
	if (Stk(1) = "const") or _
			(Stk(1) = "dim" and Stk(2) = "shared") then
		curlevel = MAX(0,curlevel - indents)
	elseif instr(" extern declare option const defint defbyte defdbl deflng defshort defsng defstr defubyte defuint defushort ",t1) then
		'' instr is faster (x2) than looping through a list if we don't want to know what token matched
		curlevel = MAX(0,curlevel - indents)
	elseif instr(" #define #dynamic #error #inclib #include #print #static #undef ", t1) then
		curlevel = MAX(0,curlevel - indents)
	else
		curlevel = MAX(indents,curlevel)
	end if

	return curlevel
end function


''-------------------------------------------------------------------------------
''
'' FUNCTION    : EndinLine()
''
'' Purpose     : Looks for THEN and EXIT
''
'' History     : Date       Reason
''               31-01-05   Created
''
''-------------------------------------------------------------------------------
function EndinLine()
	dim i, ii
	for i = 0 to ubound(BumpDowns)
		for ii = 1 to Ndx
			if ii <> Ndx and Stk(ii) = "then" then
				return TRUE
			end if
			if BumpDowns(i) = Stk(ii) and Stk(ii-1) <> "exit" then
				return TRUE
			end if
		next ii
	next i
	return FALSE
end function


''-------------------------------------------------------------------------------
''
'' FUNCTION    : FastParse(Arg)
''
'' Purpose     : Divides up the file into Tokens
''
'' History     : Date       Reason
''               31-01-05   Created
''
''-------------------------------------------------------------------------------
sub FastParse(Arg as string)
	dim cnt1=0,cnt2=0
	Ndx=1

	while Arg[cnt1] <> 0
		if Arg[cnt1] = 34 then      ''quotes - string literals
			if cnt2 then Stk(Ndx)[cnt2]=0 : Ndx +=1 : cnt2=0
			Stk(Ndx)[0] = 34
			cnt1 +=1
			while Arg[cnt1] <> 34
				cnt2 +=1
				Stk(Ndx)[cnt2] = Arg[cnt1]
				if Arg[cnt1] = 0 then exit sub
				cnt1 +=1
			wend
			cnt2+=1
			Stk(Ndx)[cnt2] = 34
			cnt2+=1
			Stk(Ndx)[cnt2]=0
			Ndx+=1
			cnt2=0
		elseif Arg[cnt1] = 32 or Arg[cnt1] = 9 then  '' spaces, tab
			if cnt2 then Stk(Ndx)[cnt2]=0 : cnt2 = 0 : Ndx+=1
		elseif Arg[cnt1] = 58 or Arg[cnt1] = 61 or Arg[cnt1] = 40 then  '' :  = (
			if cnt2 then Stk(Ndx)[cnt2]=0 : Ndx+=1
			Stk(Ndx)[0] = Arg[cnt1]
			Stk(Ndx)[1]=0 : cnt2 = 0 : Ndx+=1
		else
			if Arg[cnt1] = 39 then exit while
			Stk(Ndx)[cnt2]=Arg[cnt1] : cnt2+=1
		end if
		cnt1+=1
	wend
	Stk(Ndx)[cnt2]=0
	if cnt2 = 0 then Ndx-=1
end sub


''-------------------------------------------------------------------------------
''
'' FUNCTION    : MCASE(Arg)
''
'' Purpose     : Converts string to mixed case
''               does not need to be too fancy because it is only used with single words
''
'' History     : Date       Reason
''               24-06-05   Created
''
''-------------------------------------------------------------------------------
function MCASE(s as string) as string
	static b as string
	b = lcase(s)
	if b[0] > 96 and b[0] < 123 then b[0] = b[0] - 32
	return b
end function


''-------------------------------------------------------------------------------
''
'' FUNCTION    : strnicmp(Arg)
''
'' Purpose     : Replacement for C runtime function not implemented in Linux (?)
''
'' History     : Date       Reason
''               10-07-05   Created
''
''-------------------------------------------------------------------------------
function strnicmp(byref str1 as string, byref str2 as string, byval count as integer) as integer
	dim as integer i
	dim as integer i1, i2

	for i = 0 to count -1
		i1 = str1[i]
		i2 = str2[i]
		if i1 > 64 and i1 < 91 then i1 = i1 + 32
		if i2 > 64 and i2 < 91 then i2 = i2 + 32
		if i1 <> i2 then return i1 - i2
	next
	return 0
end function

