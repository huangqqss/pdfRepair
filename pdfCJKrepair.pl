#!/usr/bin/perl
#
# A utility for modifying metadata, add bookmark, etc, now mainly for
#	repair CJK encoding of PDF produced by
#	"S22PDF V1.0 郭力(C) pdf@home.icm.ac.cn", or other tools
#	of China, which occasionally show broken text and bookmarks.
#	See comment around &update_font below.
#
# --------------------------------
# Usage: perl ./pdfCJKrepair.pl file.pdf
# --------------------------------
#
# Perl has other modules for pdf: Text::PDF, PDF::API2, CAM::PDF.
# A simple page number like pp102 means checking that page of pdf_reference_1-7.

use feature 'switch';
use strict;
use warnings;
use utf8;
use Encode;
use Encode::Guess;

our $debug = 0;
unlink(glob('TMP.*.log'));
our $fin = $ARGV[0], my $xref_lol, my $trailer_lol;
our $file, our %xref, our %trailer;
our $max = (stat($fin))[7]; # perl will allocate this memory at start
our $eol; # keep the eol style, Acrobat likes \r, pdftk likes \n
our $update; # number of updating, or version (number of %%EOF - 1)
our $idgen_r = qr/(\d+)[\s\x00]+(\d+)[\s\x00]*/;
our $linearized = 0;
#my %type = (qw/ << dict < hex ( string [ array xref xref trailer trailer /,
#	'/'=>'name', '\d'=>'obj');
## { and } are used in function within stream, but I do not care them.
#my %paren = (qw/( ) [ ] { } < > << >> stream endstream obj endobj/, '%', '\R');
my $font_templ  = <<'END';
<<
/Type /Font /Subtype /Type0 /BaseFont /%%BaseFont%% %/Name /TT0
/Encoding /GBK-EUC-H
/DescendantFonts [ <<
/Type /Font /Subtype /CIDFontType2 /BaseFont /%%BaseFont%% %/WinCharSet 134
/CIDSystemInfo << /Registry (Adobe) /Ordering (GB1) /Supplement 2 >>
/DW 1000 /W [ 1 95 500 814 907 500 7712 7716 500 ]
/FontDescriptor /%%FontDescriptor%%
>> ]
>>
END
# pp436: Although /Type is /Font, a CIDFont is not actually a font. 
# pp411: CIDFontType2 can only be used as a component of Type0.
# FontDescriptor (pp455) in the broken font of WinAnsiEncoding, which are quit
#	simple, are different from the good CIDFontType2 font, which are more
#	complex and various.  I change some values in /FontDescriptor and
#	found no difference in display, and I guess /FontDescriptor only help
#	acroread to find a proper substitution font (pp455).
# /W really determine the display, controlling the width of every character, no
#	matter substituted font or not.  For '/W', ref: pp7 of 5094.CJK_CID.pdf.
#	More specific /W improves the display of variable width characters.
# TJ operator (pp408) show text and allowing individual glyph positioning
#	(generally adjust the space between letters); Some PDF assign the
#	position of each characters and use Tj (pp407) to show the text,
#	making the \W assignment useless.
# In Acrobat, text typeset by a TJ or Tj is recognized as an individual,
#	moving together following Touch-up; such an individual is mainly for
#	adjusting the spacing.  If need logical structure, such as word,
#	sentence, paragraph, and title, use Logical structure (pp855) may
#	improve interoperation with text editor and web browser.
# Text stream denote a paragraph like this:
#	`/P <</MCID 1>>BDC [(Hellow, world!)] TJ EMC`.  Such a paragrapha can
#	be copied and pasted as a single line, without distorting line break
#	in the middle.  Acrobat plugin of MSWord generates such logical
#	structure.  Interestingly, the plugin preserves the newline mark
#	(\r\n) in MSWord, typesetting it as `( )Tj` in the construction,
#	although it is invisible in Acrobat.  Either BDC/EMC and BT/ET mark
#	pair can be nested by the other, depending on the formatting and style
#	of the text in MSWord itself.
my %fontdescriptor = ( # obtained from various PDF with CIDFontType2
	Flags=>{ SimSun=>2+4,
		'SimSun,Italic'=>2+4+64,	KaiTi_GB2312=>2+4+64,
		'SimSun,Bold'=>2+4,		SimHei=>4,
						FangSong_GB2312=>2+4 }, # pp458
	Panose=>{ SimHei	=>'<0000 02010609060000000000>',
		WQYMicroHei	=>'<0000 02110606030804020204>',
		# This byte 00 tell ^^ acroread nothing and use AdobeHeitiStd
		KaiTi_GB2312	=>'<0500 02010609030000000000>',
		FangSong_GB2312	=>'<0500 02010609030000000000>',
		ArphicUMingCN	=>'<0000 02110306000000000000>',
		SimSun		=>'<0500 02010609030000000000>',
		#SimSun		=>'<0500 02010609000000000000>',
		#SimSun		=>'<0500 02010600000000000000>',
		# This byte 05 tell ^^ acroread (Linux) use AdobeSongStd
		#	Actually, only 00 results in Heiti, others Song.
	},
	# first 2 bytes are family class and subclass ID (pp461), given in
	#	sFamilyClass field of the OS/2 table in a TrueType font, 
	#	which is documented in Microsoft’s True-Type 1.0 Font Files
	#	Technical Specification.
	# last 10 bytes obtained with fontforge (OS/2特征) from the ttf font
);
my %fontname = (
	'/#CB#CE#CC#E5'=>'SimSun',
	'/#CB#CE#CC#E5,Italic'=>'SimSun,Italic',
	'/#CB#CE#CC#E5,Bold'=>'SimSun,Bold',
	'/#BF#AC#CC#E5_GB2312'=>'KaiTi_GB2312',
	'/#BA#DA#CC#E5'=>'SimHei',
	'/#B7#C2#CB#CE_GB2312'=>'FangSong_GB2312' );
# pp419: fontname (especially CJK) can be encoded by the host OS,
#	by the # notation.  acroread interprete these name depending on
#	environment: on Windows, use GBK, while on Linux, use UTF-8.

my $overwritefix = 0, my $updatefix = 1;
if (1==$overwritefix) { # Fix by overwriting objs
	($update, $eol, $xref_lol, $trailer_lol) = &load($fin, 0);
	#&unhide("$fin.unhide");
	&overwrite_font($font_templ, \%fontdescriptor, %fontname);
	&overwrite_outlines('S22PDF1');
	&overwrite_viewerpreferences();
	&overwrite_info('S22PDF1');
	&save( [ ], [ ], "$fin.overwrite");
}
if (1==$updatefix) { # fix by updating (appending) objs
	($update, $eol, $xref_lol, $trailer_lol) = &load($fin, 0, 'retain');
	#&save( &downdate(0, $xref_lol, $trailer_lol), "$fin.downdate");
	&save( [ ], [ %trailer ], "$fin.update", (
		&update_font($font_templ, \%fontdescriptor, %fontname),
		&update_outlines('S22PDF1'),
		&update_viewerpreferences(),
		&update_info('S22PDF1') ) );
	# Since the result file contains skipped %%EOF, versions of it cannot
	#	be recovered by simply &load($fin, -1).
}

sub load {
	my ($fin, $downdate, $retain) = @_;
	our $file;
	open(IN, $fin);
	read(IN, $file, $max);
	close(IN);
	$file=~m/^%PDF-(\d+\.\d+)(\R)/a; my $ver = $1, my $eol = $2;
	&info("Unhandled high version", $ver) if (1.4<$ver);
	$linearized = 0;
	my $prev, my @xref_l, my @trailer_l, my @eof;
	do {
		my ($eof, $xref_l, $trailer_l) = &eof($prev);
		my %trailer = @$trailer_l;
		unshift(@eof, $eof);
		unshift(@xref_l, $xref_l);
		unshift(@trailer_l, $trailer_l);
		$prev = $trailer{'/Prev'};
		&error('LOAD', 'Cannot handled encrypted PDF', %trailer)
			if (exists($trailer{'/Encrypt'}));
		if ($debug) {
			open(OUT, ">$fin.$eof.pdf");
			print OUT (substr($file, 0, $eof+1));
			# $eof+1 so as to keep linefeed at the end if there is
			close(OUT);
		}
	} until (!defined($prev));
	my $update = $#eof;
	if (defined($downdate)) {
		#if ($#eof==$downdate || -1==$downdate) { do nothing }
		$update = $downdate>=0 ? $downdate : $downdate+@eof;
		# 0>$downdate means removing last -$downdate updates,
		#	0<=$downdate means keeping first $downdate+1 updates.
		&error('LOAD', $downdate, 1+$#eof, $linearized)
			if (0>$update  || $#eof<$update);
		# In a Linearized file, EOF near the beginning is the $eof1[1],
		#	and then $eof[0], and then eof of updates.
		$file = substr($file, 0, 1+$eof[(
			(0<$linearized && 2>$update) ? 0 : $update )])
			unless (defined($retain));
		#substr($file, $eof[$update]+2) = '';
		$update = 1 if (0<$linearized && 2>$update);
		splice(@xref_l,    $update+1);
		splice(@trailer_l, $update+1);
	}
	our %xref = map(@$_, @xref_l);
	# pushed at last overwrite the previous, pdf and perl are the same
	#foreach my $k (keys(%xref)) {
	#	if (-1==$xref{$k} && $k ne '0 65535') {
	#		die("$k");
	#	}
	#}
	our %trailer = @{$trailer_l[-1]};
	return($update, $eol, \@xref_l, \@trailer_l);
}

sub save {
	my ($xref_l, $trailer_l, $fout, @obj) = @_;
	open(OUT, ">$fout.pdf");
	print OUT ($file);
	my @xref = @$xref_l; # Unless reviving old obj, should be empty
	my $seek = length($file);
	if (0<@xref || 0<@$trailer_l || 0<@obj) {
		my $bin = "%The original PDF ends at $seek byte$eol";
		print OUT ($bin);
		$seek += length($bin);
	}
	for (my $iobj = 0; @obj>$iobj; $iobj += 2) {
		my $idgen = $obj[$iobj];
		$idgen=~s/[\s\x00]*(?:R|obj)$//;
		push(@xref, $idgen, $seek);
		my $bin = join($eol,
			("$idgen obj", $obj[$iobj+1], 'endobj')) .$eol;
		print OUT ($bin);
		$seek += length($bin);
	}
	if (0<@xref && 0<@$trailer_l) {
		my %trailer = @$trailer_l;
		$trailer{'/Prev'} = $trailer{startxref}
			if (exists($trailer{startxref}));
		print OUT (&neweof( &newxref(@xref),
			&newtrailer(%trailer), $seek));
	}
	close(OUT);
	return();
}

sub debug {
	my ($sub, $bin, $flog) = @_;
	return() unless ($debug);
	print(join(', ', caller()), "\n") if (2==$debug);
	open(LOG, '>>TMP.' .(defined($flog)?$flog:'tmp') .'.log');
	if ('' eq $sub) {
		print LOG ($bin, "\n");
	} elsif ($sub=~m/:$/) {
		print LOG ($sub, $bin, "\n");
	} else {
		print LOG ($sub, sprintf('% 10d', pos($file)), ":$bin\n");
	}
	close(LOG); # if recursive, use $log instead LOG to avoid close file
	return();
}

sub info {
	my ($keyword, @info) = @_;
	print("!!$keyword: ", join(',', @info), "!\n");
	return();
}

sub error {
	my ($keyword, @info) = @_;
	&debug("$keyword:", @info);
	print("!!$keyword: \n\t", join("\n\t", @info), "\n");
	die( '!!Broken obj!');
}

sub cmpxref { # cmp for sort is special, see perldoc
	#my ($aa, $bb) = map { my ($id, $gen) = split(/ /, $_);
	#	$id+$gen/1e6 } ($a, $b);
	my ($aa, $bb) = map(($_=~m/^$idgen_r/a)?($1+$2/1e6):0.0, ($a, $b));
	# regexp slower but robuster than split(), which requires $idgen
	#	to be normalized
	$aa<=>$bb;
}

sub obj { # parse indirect object ($id $gen obj ... endobj)
	my ($offset) = @_;
	if ($offset=~m/^$idgen_r(?:R|obj)?$/) { # less strict
		my $id = $1, my $gen = $2;
		$offset = $xref{"$id $gen"} or &error('OBJ', ":$offset");
		return($offset) if (-1==$offset);
	}
	my $p = pos($file);
	pos($file) = $offset;
	&debug('OBJ:', substr($file, $offset, 60));
	$file=~m/\G[\s\x00]*$idgen_r(?:obj)\b/ga or
		&error('OBJ', substr($file, $offset, 60));
	my ($end, $offset_l, $type, @obj) = &parse($offset);
	pos($file) = $p; # restore pos() after the call
	return($offset, $end, $type, @obj);
}

sub newobj {
	my ($type, @obj) = @_; # @obj is &content(), without << and >>
	my $l = qr'<<|[{[(</%]'; # left delimiter
	my $r = qr/>>|[]})>]/; # right delimiter
	my $stream;
	if ('stream' eq $type) {
		$stream = pop(@obj);
		&error('NEWOBJ') unless ('' eq pop(@obj)); 
	}
	my $bin = '';
	my $length = 0;
	for (my $iobj = 0; @obj>$iobj; $iobj++) {
		my $obj = $obj[$iobj];
		if ( 0==$iobj%2 && $obj!~m|^/| && ('dict' eq $type ||
			'stream' eq $type) ) {
			$obj = "/ERRORRECOVERY"; # fault recovery
			&info('Broken dict', @obj); # issue warning
		}
		my $binend = substr($bin, -1);
		my $b;
		if (255<$length+length($obj)) {
			$b .= "$eol$obj";
			$length = 0;
		} elsif ($binend=~m=^(|[]})>/])$= || $obj=~m=^[[{(</]=) {
			$b .= $obj; # save space
		} else {
			$b .= " $obj";
		} # It seems Acrobat Distiller packs dict in similar manner
		$bin .= $b;
		$length += length($b);
	}
	if ('array' eq $type) {
		$bin = "[$bin]";
	} elsif ('dict' eq $type) {
		$bin = "<<$bin>>";
	} elsif ('stream' eq $type) {
		$bin = "<<$bin>>" .$eol ."stream\r\n$stream\r\nendstream";
	}
	return($bin);
}

sub xref {
	my ($offset) = @_;
	my ($end, @obj);
	pos($file) = $offset;
	$file=~m/\G[\s\x00]*xref\R/ga or &error("XREF", $offset);
	while ($file=~m/\G(\d+) (\d+) *\R/ga) {
		my $id = $1;
		for (my $total = $2; 0<$total; $total--) {
			$file=~m/\G(\d{10})\ (\d{5})\ ([nf])
				(?:\ \n|\ \r|\r\n)/gax or
				&error("XREF", $total);
			my $offset = ('n' eq $3) ? "1$1" - 10000000000 : (
				('f' eq $3) ? -1 : &error('XREF', $1, $2, $3));
			# $offset==0 and $gen==65535 is valid (pp95), I guess
			#	it indicates obj absense, like obj 0 0.
			my $gen = "1$2"-100000;
			push(@obj, "$id $gen", $offset);
			#if ('f' eq $3) {
			#	&error('XREF', $id, $nextfreeobj)
			#		unless ($id==$nextfreeobj);
			#	$nextfreeobj = "1$1" - 10000000000;
			#}
			# The generation number is used for updating,
			#	but Acrobat 6 does not recycle obj
			#	number, see pp1102, item 16.
			# Also, several copies of an object with the
			#	same id and gen can be in the same
			#	file, the most recent xref has effects.
			# It seems deleted obj (id+gen) cannot be reused
			#	later.  I can only change a obj by appending
			#	a new indirect obj and update its xref, delete
			#	a obj by free its xref, add a totally new obj
			#	by making a new indirect obj and make its xref,
			#	reuse a obj id by appending a new obj and make
			#	its xref by reuse a freed id but increase its
			#	generation number.  Anyway, the previous free
			#	id+gen cannot be cover by later updating of
			#	xref, it is simply wrong.
			$id++;
		}
		$end = pos($file); # unmatch will reset pos($file) to undef
	}
	return($end, @obj);
}

sub newxref {
	my (%offset) = @_;
	$offset{'0 65534'} = -1; # later, $gen++ and become 65535
	my @id = sort cmpxref (keys(%offset));
	my %id;
	$id{(split(/ /, $_))[0]}++ foreach (@id);
	&error('NEWXREF', %offset) if (0<grep(1<$_, values(%id)));
	undef(%id);
	my @first, my @count, my @free;
	my $first = 0, my $count = 0, my $last = -1;
	foreach my $idgen (@id) {
		my ($id, $gen) = split(/ /, $idgen);
		push(@free, $id) if (-1==$offset{$idgen});
		if ($last+1==$id) {
			$count++;
		} else {
			push(@first, $first);
			push(@count, $count);
			$first = $id;
			$count = 1;
		}
		$last = $id;
	}
	push(@first, $first);
	push(@count, $count);
	shift(@free); push(@free, 0);
	$last = -2;
	my $bin = "xref$eol";
	foreach my $idgen (@id) {
		my ($id, $gen) = split(/ /, $idgen);
		if ($last+1!=$id) {
			$first = shift(@first);
			$count = shift(@count);
			$bin .= sprintf("%d %d$eol", $first, $count);
		}
		my $offset = $offset{$idgen}, my $n = 'n';
		if ($offset==-1) {
			$offset = shift(@free);
			$n = 'f';
			$gen++;
		}
		$bin .= sprintf("%010d %05d %s\x0D\x0A", $offset, $gen, $n);
		$last = $id;
	}
	return($bin);
}

sub trailer {
	my ($offset) = @_;
	pos($file) = $offset;
	$file=~m/\G[\s\x00]*trailer\R/ga or &error('TRAILER', $offset);
	my ($end, $offset_l, $type, @obj) = &parse(pos($file));
	($type, @obj) = &content(substr($file, pos($file), $end-pos($file)));
	return($end, @obj);
}

sub newtrailer {
	my (%trailer) = @_;
	my @trailer = map {$_, $trailer{$_}} (
		grep(exists($trailer{$_}), ( '/Size', '/Prev',
		'/XRefStm', '/Root', '/Encrypt', '/Info', '/ID' )) );
	return('trailer' .$eol .&newobj('dict', @trailer));
}

sub eof {
	my ($offset) = @_;
	my %offset;
	if (!defined($offset)) {
		$offset{eof} = rindex($file, '%%EOF');
		&error('EOF', $offset{eof}, length($file), "!!Not find EOF!")
			if ($offset{eof}+1024<length($file));
		# 1024 is documented in pdf_reference_1-1
		$offset{startxref} = rindex($file, 'startxref', $offset{eof});
	} else {
		$offset{xref} = $offset;
		$offset{startxref} = index($file, 'startxref', $offset{xref});
		$offset{eof} = index($file, '%%EOF', $offset{xref});
	}
	my $obj = substr($file, $offset{startxref}-1,
		$offset{eof}+5-($offset{startxref}-1));
	$obj=~m/^\Rstartxref\R(\d+)\R%%EOF$/sxa or &error('EOF', $obj);
	$offset = $1 unless (defined($offset));
	$offset{xref} = $offset;
	if ($offset!=$1) {
		our $linearized++;
		# 2==$linearized means the Linearized PDF has been updated
		#	and is nolonger Linearized (strictly speaking), but
		#	I should be careful when downdate it.
		&info('Linearized', "$linearized, $1!=$offset<"
			.$offset{startxref});
		# for Linearized, 0==startxref is a constraint.
	}
	my @xref, my @trailer;
	($offset{xref_end}, @xref) = &xref($offset{xref});
	$offset{trailer} = index($file, 'trailer', $offset{xref_end});
	($offset{trailer_end}, @trailer) = &trailer($offset{trailer});
	push(@trailer, 'startxref', $offset{xref});
	# use @trailer to keep startxref, because this offset is useful later.
	return($offset{eof}+5, \@xref, \@trailer);
}

sub neweof {
	my ($xref, $trailer, $startxref) = @_;
	return(join($eol, ($xref, $trailer, 'startxref', $startxref, '%%EOF')));
}

sub content { # dereference indirect object (only once, not recursively)
	my ($bin) = @_;
	my $end, my $offset_l, my $type, my @obj, my $offset;
	if ($bin=~m/^$idgen_r(?:R)$/) {
		($offset, $end, $type, @obj) = &obj($bin);
		#@obj = &content(@obj) if (1==@obj); # need not recursive
		&error('CONTENT') unless (shift(@obj)=~m/^$idgen_r(?:obj)$/);
		&error('CONTENT') unless (pop(@obj) eq 'endobj');
	} else {
		($end, $offset_l, $type, @obj) = &parse(0, \$bin);
		# avoid special usage of &parse(0, \$bin) elsewhere for clarity
		#	(only &parse($offset, \$file) elsewhere)
	}
	if ('dict' eq $type) {
		&error('CONTENT') unless (shift(@obj) eq '<<');
		&error('CONTENT') unless (pop(@obj) eq '>>');
	} elsif ('array' eq $type) {
		&error('CONTENT') unless (shift(@obj) eq '[');
		&error('CONTENT') unless (pop(@obj) eq ']');
	} elsif ('stream' eq $type) {
		&error('CONTENT') unless (shift(@obj) eq '<<');
		&error('CONTENT') unless ($obj[-2] eq '>>');
		$obj[-2] = ''; # keep even number of members
	} # guaranttee returning @obj that can become %obj.
	return($type , @obj);
}

sub parse {
my ($offset, $bin_r) = @_;
my $c = qr=[^]{}()<>/%\s\x00[]=; # regular character
$bin_r = \$file unless (defined($bin_r));
my $offset_old = pos($$bin_r);
pos($$bin_r) = $offset;
my $end = $offset, my @offset, my $type = '', my @obj, my @pos;
my $last = 0;
while ($$bin_r=~m=\G[\s\x00]*(<<|>>|[](){}<>/%[]|$idgen_r(?:obj|R)|$c+)=ga) {
	my $m = $1;
	&debug('PRS:', "$m|@obj");
	if ($m=~m/^(true|false|null|[-+]?[\d.]+|$idgen_r(?:R))$/) {
		# literal objects, simply push
	} elsif ('/' eq $m) { # need look forward
		$$bin_r=~m/\G($c+)/ga;
		$m =  "/$1"; # name
	} elsif ('<' eq $m) { # string (hexadecimal encoding)
		$$bin_r=~m/\G([^>]*)>/ga;
		$m =  "<$1>";
	} elsif ('%' eq $m) { # need look forward
		$$bin_r=~m/\G[^\r\n]*\R/ga; # comment
		next;
	} elsif ('(' eq $m) { # literal string, may contain nesting ()
		# literal string can contain CJK directly
		pos($$bin_r) -= length($m);
		my $str = substr($$bin_r, pos($$bin_r), 32767);
		# length is limited, pp992
		$str=~s/\\\\|\\[()]/  /g; # handle backslash escaped
		$str=~m/\G(\(([^()]|(?1))*\))/ or &error('String', $str);
		# or /\(([^()]|(?R))*\)/ but cannot be /\G\(([^()]|(?R))*\)/.
		$m = substr($$bin_r, pos($$bin_r), length($1));
		pos($$bin_r) += length($m);
	} elsif ('<<' eq $m || '[' eq $m) { # recursive, only do shallow parse
		push(@pos, pos($$bin_r)-length($m));
	} elsif ('>>' eq $m || ']' eq $m) {
		&error('Dict/Array', $m) if (0==@pos); # encounter >> before <<
		my $p = pop(@pos);
		$type = ('>>' eq $m)?'dict':'array' if (0==@pos); # and last
		$m = substr($$bin_r, $p, pos($$bin_r)-$p) if (1==@pos);
	} elsif ('stream' eq $m) {
		&error('Stream') unless (0==@pos); # following a complete dict
		my $p = pos($$bin_r)-length($m);
		$type = 'stream';
		$$bin_r=~m/\G(\r?\n)/ga; # never \r alone
		# pp60: All streams must be indirect objects, and the stream
		#	dictionary must be a direct object.
		my %obj = map {$obj[$_]=>$_} (0 .. $#obj); # proceeding dict
		pos($$bin_r) += (&content($obj[$obj{'/Length'}+1]))[1];
		$$bin_r=~m/\G\R?endstream/ga or &error('Stream');
		$m = substr($$bin_r, $p, pos($$bin_r)-$p);
	} elsif ($m=~m/^($idgen_r)(obj)$/) {
		#&error('id_gen_obj'); # for indirect obj should ever use &obj()
	} elsif ('endobj' eq $m) {
		$last = 1;
	} elsif ('startxref' eq $m) { # end trailer
		pos($$bin_r) -= length($m);
		$last = 1;
	} else {
		&error('Parse', $end, $m, @obj);
	}
	if (1>=@pos) {
		push(@obj, $m);
		push(@offset, pos($$bin_r)-length($m));
		# $end_of_obj = $start_of_obj+length($m), need not recording.
	}
	$end = pos($$bin_r);
	last if ($last);
}
pos($$bin_r) = $offset_old; # restore pos() after the call
return($end, \@offset, $type, @obj);
}

sub unhide {
	my ($fout) = @_;
	my @end;
	foreach my $idgen (sort cmpxref (keys(%xref))) {
		my ($offset, $end, $type, @obj) = &obj($idgen);
		next if (-1==$offset);
		&debug('UH:', substr($file, $offset, $end-$offset)
			."\r\n\r\n" .join($eol, @obj), $idgen);
		push(@end, $idgen, $end);
	}
	open(OUT, ">$fout");
	my %end = @end;
	my @idgen = sort { $end{$a} <=> $end{$b} } (keys(%end));
	print OUT (substr($file, 0, $xref{$idgen[0]}), "\r\n\r\n");
	for (my $i = 0; $#idgen>$i; $i++) {
		my $bin = substr($file, $end{$idgen[$i]},
			$xref{$idgen[$i+1]}-$end{$idgen[$i]});
		next if ($bin=~m/^[\s\x00]+$/);
		print OUT ($bin, "\r\n\r\n");
	}
	print OUT (substr($file, $end{$idgen[-1]}, $max));
	close(OUT);
	return();
}

sub downdate {
# remove append modification by free those objects.
# This sub is mainly for testing, not for really use.
# The result display has been verified by evince and acrobat, report no error;
#	by diffpdf, report the same as the other that is simply truncated at
#	the previous %%EOF; by pdftk, by converting with
#	`pdftk 1.pdf output 1out.pdf uncompress` and then vimdiff both files,
#	checking by eyes notices the only difference from the other with simple
#	truncation is the absense of /Info obj (indeed I do not refer it in
#	the new xref and trailer.
	my ($downdate, $xref_lol, $trailer_lol) = @_;
	&info('DOWNDATE', '&downdate is useless; For downdate, '
		.'use &load() is convinient, fast, and safe');
	my @xref_l = @$xref_lol;
	my $update = $downdate>=0 ? $downdate : $downdate+@xref_l;
	&error('LOAD', $downdate, 1+$#xref_l, $linearized)
		if (0>$update || $#xref_l<$update);
	$update = 1 if (0<$linearized && 2>$update);
	my %xref     = map(@$_, @xref_l[0 .. $update]);
	my %xrefundo = map(@$_, @xref_l[$update+1 .. $#xref_l]);
	foreach my $idgen (keys(%xrefundo)) {
		if (-1==$xrefundo{$idgen}) {
			my ($id, $gen) = split(/ /, $idgen);
			my @idgen = sort cmpxref (
				grep(/^$id [0-9]+$/, keys(%xref)));
			# if only undo one version, then it can be simpler.
			if (0<@idgen) {
				# Revive the obj of newest old generation.
				delete($xrefundo{$idgen});
				$idgen = $idgen[-1];
			}
		}
		if (exists($xref{$idgen})) {
			$xrefundo{$idgen} = $xref{$idgen};
		} else {
			$xrefundo{$idgen} = -1;
		}
	}
	my %t0 = @{$$trailer_lol[-1]};
	my %t1 = @{$$trailer_lol[$update]};
	return( [ %xrefundo ], [ '/Size', $t0{'/Size'}, '/Root', $t1{'/Root'},
		'/Prev', $t0{startxref} ] );
	# I hope objs of the same id but larger gen, residing in the undone
	#	updating, are negelected by PDF readers.  I do not know if it
	#	complies the specification of PDF.  A section of xref can hold
	#	only one obj id (see pp94), but syntax of reference (id gen R)
	#	and definition (id gen obj ... endobj) allows the co-existence
	#	of objs with the same id but different gen.  However, the
	#	specification of incremental gen number in xref for freed objs
	#	suggests freeing cannot be redo, though the id can be re-used,
	#	the gen not.
	# Downdating too many can make the output pdf broken (with missing obj).
}

sub list { # list objs by a path, like ls on Unix
	my (@key) = @_;
	@key = map("/$_", split(/\//, join('', @key)));
	my $key, my @bin;
	$key = shift(@key);
	if ('/' eq $key) {
		$key = shift(@key); # @key starts with / and $key[0] is empty
	} else {
		$key=~s|^/||; # original $key[0] has no /
	}
	if ('/Root' eq $key) {
		@bin = ( $trailer{$key} );
	} elsif ('/Info' eq $key) {
		@bin = ( $trailer{$key} );
	} elsif ($key=~m/^\d+\s\d+\sR/) { # can be repeating refs
		my @obj = split(/\s+/, $key);
		@bin = map("$obj[$_*3] $obj[$_*3+1] R", (0 .. @obj/3));
	} elsif ($key=~m/^<</) { # a dict
		# need many changes, because now @key cannot have too many '/'.
	} else {
		my $name;
		if ($key=~m|^/|) {
			$name = '/Type'; # $key[0] is /Type of obj
		} else {
			$name = "/$key"; # $key[0] is /$name
			$key = shift(@key);
		}
		foreach my $idgen (keys(%xref)) { # scan all objs
			my ($offset, $end, $type, @obj) = &obj($idgen);
			next if (-1==$offset or 'dict' ne $type);
			($type, @obj) = &content($idgen);
			my %obj = @obj;
			push(@bin, "$idgen R") if (exists($obj{$name}) &&
				$key eq $obj{$name});
		}
	}
	my $trace_key; # following the obj ref along the path
	foreach my $k (@key) {
		my @value = ( );
		$trace_key .= $k;
		if ($k=~s|^/%||) { # % is comment in pdf, reuse here for regexp
			$k = qr|^/$k$|; # force the anchor
		}
		foreach my $b (@bin) {
			my ($type, @dict) = &content($b);
			my %dict = @dict;
			if ('array' eq $type) {
				foreach my $a (@dict) { # @dict is array
					my ($type, %dict) = &content($a);
					push(@value, $dict{$k});
				} # @bin explosion here
			} elsif ('Regexp' eq ref($k)) {
				my @keys = grep($k, keys(%dict));
				push(@value, map($dict{$_}, @keys));
			} elsif ('/Kids%%' eq $k) { # tree
				push(@value, &tree($b));
			} elsif ($k=~m=^(/Names|/Nums)%%$=) {
				my ($type, %dict) = &content($dict{$1});
				&error('LIST', $type, %dict)
					unless ('array' eq $type);
				push(@value, values(%dict)); # or &tree2dict()
			} elsif ($k=~m=^(/First|/Next|/FirstNext)%%$=) {
				push(@value, &chain($1, $b));
			} elsif (exists($dict{$k})) {
				push(@value, $dict{$k});
			} else {
				&debug("$b:", "$k:@dict");
			}
		}
		my %value;
		foreach my $v (@value) {
			$value{$v}++ if (defined($v));
		}
		@bin = sort(keys(%value));
		&debug("LIST:", "@value || @bin") if ($debug);
	}
	return(sort(@bin));
}

sub tree {
	my ($bin) = @_;
	my ($type, @dict) = &content($bin);
	&debug('TREE:', $bin) if (0!=@dict%2);
	my %dict = @dict;
	return($bin) unless ('dict' eq $type && exists($dict{'/Kids'}));
	my @obj;
	($type, @obj) = &content($dict{'/Kids'});
	# pp162: /Kids seems an indirect array containing indirect refs.
	&error('TREE:', $type, @obj) unless ('array' eq $type);
	my @leaf = map(&tree($_), @obj);
	return(@leaf);
	# pp143: @leaf is a /Names array or /Nums array, and may be pages,
	#	whose tree has no /Names or /Nums
	# One more step is needed to obtain the /Names or /Nums array.
}

sub tree2dict {
# this kind of dict can have any strings as keys, violating the syntax of
#	path, thus I have to handle it independently.
	my (@bin) = @_;
	my @dict;
	foreach my $bin (@bin) {
		my ($type, %dict) = &content($bin);
		my $key, my @d;
		if (exists($dict{'/Names'})) {
			$key = '/Names';
		} elsif (exists($dict{'/Names'})) {
			$key = '/Nums';
		} else {
			&error('TREE2DICT', $type, %dict);
		}
		($type, @d) = &content($dict{$key});
		&error('TREE2DICT', $type, @d) unless ('array' eq $type);
		push(@dict, @d);
	}
	return(@dict);
}

sub chain { # pp584: for /Outlines
	my ($key, @node) = @_; # entry nodes of the chain
	my $idx = 0;
	while ($idx<@node) {
		my ($type, %dict) = &content($node[$idx]);
		if ('/FirstNext' eq $key) {
			foreach my $k ('/First', '/Next') {
				push(@node, $dict{$k}) if (exists($dict{$k}));
			} # or recursively call &chain
		} else {
			push(@node, $dict{$key}) if (exists($dict{$key}));
		}
		$idx++;
		&debug("CHAIN:", "@node");
	}
	return(@node);
}

sub squeeze {
# remove unnecessary spaces between first layer objs.  Serious squeezing can be
#	achieved by recursively squeezing all layers, or by compressed stream.
	my ($bin, $length, $pos) = @_;
	$pos = length($bin) unless (defined($pos));
	my $white = ' ' x $length;
	my ($end, $offset_l, $type, @obj) = &parse(0, \$bin);
	my @offset = @$offset_l;
	if ('' eq $type) {
		# stub, need implemented
		&error('SQUEEZE', @offset);
		my $obj = $obj[0]; # is other simple type
		if ($obj=~m/^<.*>$/) {
			$obj=~s/[\s\x00]//g; # or pack() into literal string
		}
		if (0==$pos) {
			return("$white$obj", $pos);
		} else {
			return("$obj$white", length($obj));
		}
	}
	if ($obj[0]=~m/^$idgen_r(?:obj)$/) {
		shift(@obj); pop(@obj); shift(@offset); pop(@offset);
	}
	my $delim = qr|^[]{}()<>/[]$|;
	for (my $i = $#offset; -1<$i; $i--) {
		my $oflast = (0==$i) ? 0 : ($offset[$i-1]+length($obj[$i-1]));
		my $offset = $offset[$i];
		my $len = $offset-$oflast;
		my $clast = (0==$i) ? '' : substr($obj[$i-1], -1);
		my $char = substr($obj[$i], 0, 1);
		my $space = substr($bin, $oflast, $len);
		my $gap = ($clast=~m/$delim/ || $char=~m/$delim/) ? '' : (
			($space=~m/\R/) ? ' ' : "\r" ); # acrobat prefer \r
		substr($bin, $oflast, $len) = $gap;
		$length -= $len-length($gap);
		$pos -= $len-length($gap) if ($pos>=$offset);
		last if (0>$length);
	}
	&error('SQUEEZE', $length) if (0<$length); # not powerful enough
	substr($bin, $pos, 0) = $white . (' ' x -$length);
	return($bin, $length, $pos);
}

sub overwrite {
	my ($idgen, $bin, $pattern, $pos) = @_;
	my $len = length($bin);
	my ($offset, $end, $type, @obj) = &obj($idgen);
	my $len_old = $end-$offset;
	my $obj_old = substr($file, $offset, $len_old);
	my $obj = $obj_old;
	unless (defined($pattern)) {
		$pattern = qr/^$idgen_r(?:obj)[\s\x00]/; # keep a space
		$pos = 0;
	}
	$pattern = quotemeta($pattern) unless ('Regexp' eq ref($pattern)); #\Q\E
	$obj=~m/$pattern/g or &error('OVERWRITE', $pattern, $obj);
	my $cancel = 0;
	if (defined($pos)) { # $pattern defines an anchord
		$pos += pos($obj);
		$obj=~s/(\R)./$1%/g; # comment out all lines
		# for $obj in one line, this approach is not applicable.
		my $endobj = $eol .'endobj';
		my $l = length($endobj);
		if ($pos+$len+$l>$len_old) {
			&debug('OVERWRITE:',
				"$pos+$len+1+$l>$len_old:$idgen:$bin");
			$cancel = 1;
		}
		substr($obj, $pos, $len+1) = "$bin%";
		substr($obj, -$l, $l) = $endobj;
		# because $bin become "$eol$bin%", here protect endobj.
	} else { # $pattern is a range to be overwritten
		my $l = length($&);
		$pos = pos($obj)-$l;
		my $ll = $len-$l;
		($obj, $ll, $pos) = &squeeze($obj, $ll, $pos) if (0<$ll);
		substr($obj, $pos, $len-$ll) = $bin .(' ' x -$ll);
		# if $bin begins and ends with delimiters like <>()[], spaces
		#	around $bin can be removed, but at the moment I do not
		#	handle the situation.
		$cancel = 1 if (0<$ll);
	}
	if (1==$cancel) {
		&info('Overwrite', "$idgen cannot be overwritten");
		return();
	}
	substr($file, $offset, $len_old) = $obj;
	#$obj_old = substr($file, $offset, $len_old, $obj); # segmentation fault
	return($obj_old);
}

sub overwrite_dict { # better approach to update a dict than &squeeze.
	my ($dict_l, @new) = @_;
	my %new = @new;
	my @dict = @$dict_l;
	my %idx = map {$dict[$_*2]=>$_*2} (0 .. @dict/2-1);
	my %delete;
	foreach my $key (map($new[2*$_], (0 .. @new/2-1))) {
		if ($key=~m|^(/[^%]+)%$|a && exists($idx{$1})) {
			$dict[$idx{$1}] = $new{$key}; # update the key
		} elsif ($key=~m|^/[^%]+$|a) {
			if (exists($idx{$key})) { # update the value
				$dict[$idx{$key}+1] = $new{$key};
			} else {
				push(@dict, $key, $new{$key}); # new key=>value
			}
		} elsif ($key=~m|^(/[^%]+)%%$| && '' eq $new{$key}) {
			$delete{$idx{$1}} = 1; # delete the key-value pair
			$delete{$idx{$1}+1} = 1;
		} else {
			&debug('OVERDICT', join(',', %new));
		}
	}
	return(@dict[grep(!exists($delete{$_}), (0 .. $#dict))]);
}

sub textdecode {
	my ($bin, $encDefault, $lang) = @_;
	my %ansi = qw/ CN cp936 TW big5-eten JP shiftjis /;
	my %esc = ('n'=>"\n", 'r'=>"\r", 't'=>"\t", 'b'=>"\b",
		'f'=>"\f", '('=>'(', ')'=>')', "\\"=>"\\");
	if ('S22PDF1' eq $encDefault) {
	# BOM for UTF-16BE; PDF 1.7 allows 2 types of text: PDFDocEncoding and
	#	UTF-16BE with BOM. See pdf_reference_1-7 pp158.
	# old acrobat seemed to allow localized interpretation of
	#	PDFDocEncoding such as GBK, but now it is forced to be Latin1.
	# Somebody guesses that most troublesome PDFs are produced by Fangzheng
	#	Apabi reader, and Apabi can read these file without trouble.
	#	So obviously that is a marketing strategy.
		return($bin) if ($bin=~s/^\(\xFF\xFE/\(\xFE\xFF/);
		return($bin) if ($bin=~m/^\(\xFE\xFF/);
		return($bin) if ($bin=~s/^<FFFE/<FEFF/);
		return($bin) if ($bin=~m/^FEFF/);
		&debug('TXD:', "$bin"); # simple approach is not viable.
		$lang = 'CN';
		$encDefault = $ansi{$lang};
	} elsif ('S22PDF2' eq $encDefault) {
		&error('TEXTDECODE', "$encDefault not implemented");
	}
	if ($bin=~m/^\((.*)\)$/) {
		$bin = $1;
		$bin=~s/\\([nftbf()\\])/$esc{$1}/ge;
		$bin=~s/\\(\d{1,3})/chr($1)/ge;
	} elsif ($bin=~m/^<([a-h\d\s\x00]*)>$/i) {
		$bin = $1;
		$bin=~s/[\s\x00]//g;
		my $newbin;
		for (my $i = 0; length($bin)>$i; $i += 2) {
			my $code = substr($bin, $i, 2);
			$newbin .= pack('C', hex("0x$code"));
		}
		$bin = $newbin;
		# if the pdf is encrypted and decrypted by PDF Password Cracker,
		#	literal string become hexadecimal encoded
	} else {
		&error('TEXTDECODE', $bin);
	}
	my $encBOM = $ansi{$lang}, my $encGuess = $ansi{$lang};
	if ($bin=~s/^\xFE\xFF//g) {
		$encBOM = 'UTF-16BE';
	} elsif ($bin=~s/^\xFF\xFE//g) {
		$encBOM = 'UTF-16LE';
	} elsif ($bin=~s/^\xEF\xBB\xBF//g) {
		$encBOM = 'UTF-8';
	}
	my %suspect = (
		CN=>[ qw/ cp936 UTF-16BE euc-cn / ],
		TW=>[ qw/ cp950 big5-eten big5-hkscs / ],
		JP=>[ qw/ shiftjis euc-jp 7bit-jis/ ] );
	if (0) { #FIXME: sometimes guess_encoding() is broken
		my $decoder = guess_encoding($bin, @{$suspect{$lang}});
		$encGuess = $decoder->name() if (ref($decoder));
	}
	foreach my $enc ($encDefault, $encBOM, $encGuess) {
		&debug('Dec:', "$enc " .encode('UTF-8', decode($enc, $bin)));
	}
	$bin = decode($encBOM, $bin);
	$bin = "\xFE\xFF" .encode('UTF-16BE', $bin)
		unless ($bin=~m/^[[:ascii:]]*$/);
	%esc = reverse(%esc);
	$bin=~s/([\\\n\f\t\b\f()])/"\\$esc{$1}"/ge;
	return("($bin)");
}

sub overwrite_info {
my ($encDefault) = @_;
my ($idgen) = &list('/Info');
return() unless (defined($idgen));
my ($type, @dict) = &content($idgen);
my %dict = @dict;
&overwrite($idgen, &newobj('dict', &overwrite_dict(\@dict,
	map {$_, &textdecode($dict{$_}, $encDefault)} (
	grep(exists($dict{$_}), ( '/Author', '/Creator', '/Title', '/Subject',
		'/Keywords' ))))));
# /Producer (S22PDF V1.0 1ùá|(C) pdf@home.icm.ac.cn) too long to be encoded.
return();
}

sub overwrite_viewerpreferences { # fix /ViewerPreferences (pp557)
my ($idgen) = &list('/Root');
my ($type, %catalog) = &content($idgen);
my $key = '/ViewerPreferences';
&overwrite($idgen, '<< >>', $catalog{$key}) if (exists($catalog{$key}));
return();
}

sub overwrite_outlines { # fix outlines (pp586).
my ($encDefault) = @_;
my (@outline) = &list('/Root/Outlines/FirstNext%%');
foreach my $outl (@outline) {
	my %act, my $title;
	my ($type, %obj) = &content($outl);
	#(exists($obj{'/Type'}) && '/Outlines' eq $obj{'/Type'});
	unless (exists($obj{'/A'}) && exists($obj{'/Title'})) {
		&debug('FOL:', join(',', keys(%obj)));
		next;
	}
	# change action to destination (pp647, pp581)
	($type, %act) = &content($obj{'/A'});
	if ( #exists($act{'/Type'}) && '/Action' eq $act{'/Type'} &&
		exists($act{'/S'}) && '/GoToR' eq (&content($act{'/S'}))[1] &&
		exists($act{'/F'}) && "($fin)" eq
		&textdecode((&content($act{'/F'}))[1], $encDefault) ) {
		if ($obj{'/A'}=~m/^$idgen_r(?:R)$/) {
			&overwrite($outl, '/Dest', qr|/A|);
			&overwrite($obj{'/A'}, "$eol$act{'/D'}",
				qr|/D[\s\x00]+\[|, -2);
		} else {
			&overwrite($outl, "/Dest $act{'/D'}",
				qr|/A[\s\x00]+$obj{'/A'}|);
		}
	}
	($type, $title) = &content($obj{'/Title'});
	my $bin = &textdecode($title, $encDefault);
	if ($obj{'/Title'}=~m/^$idgen_r(?:R)$/) {
		&overwrite($obj{'/Title'}, $bin);
	} else {
		&overwrite($outl, $bin, $title);
	}
}
return();
}

sub overwrite_font {
my ($font_templ, $fontdescriptor_h, %fontname) = @_;
my (@f1) = ( &list('/Root/Pages/Kids%%/Resources/Font/%.*'),
	&list('/Root/Pages/Resources/Font/%.*') );
my %fontdescriptor = %$fontdescriptor_h;
foreach my $f (@f1) {
	my ($type, %obj) = &content($f);
	next unless (exists($obj{'/Subtype'}) &&
		'/TrueType' eq $obj{'/Subtype'} &&
		exists($obj{'/Encoding'}) && 
		'/WinAnsiEncoding' eq $obj{'/Encoding'});
	unless (exists($obj{'/BaseFont'}) &&
		exists($fontname{$obj{'/BaseFont'}})) {
		&info("Unhandled font", $obj{'/BaseFont'});
		next;
	}
	my $name = $fontname{$obj{'/BaseFont'}};
	&info("Fix font", "$obj{'/BaseFont'}=>$name");
	my $font = $font_templ;
	$font=~s|/%%BaseFont%%|/$name|g; # (name) not work
	my @fixfd = ( '/Type', '/FontDescriptor',
		'/FontName', "($name)", # can be /name
		'/Flags', $fontdescriptor{Flags}{$name},
		'/Style', "<< /Panose $fontdescriptor{Panose}{$name} >>" );
	#$font=~s|/%%$_%%|$fontdescriptor{$_}{$name}|
	#	foreach (keys(%fontdescriptor));
	if (exists($obj{'/FontDescriptor'})) {
		my ($type, @fontdescriptor) = &content($obj{'/FontDescriptor'});
		@fixfd = &overwrite_dict(\@fontdescriptor, @fixfd);
	}
	my $fontdescriptor = &newobj('dict', @fixfd);
	$font=~s|/%%FontDescriptor%%|$fontdescriptor|;
	$font=~s/\n/$eol/g;
	my $bin_old = &overwrite($f, $font);
}
return();
}

sub update_info {
my ($encDefault) = @_;
my ($idgen) = &list('/Info');
&error('Info', $idgen) unless ($idgen=~m/^$idgen_r(?:R)$/);
my ($type, @dict) = &content($idgen);
my %dict = @dict;
return($idgen, &newobj( 'dict', &overwrite_dict(\@dict,
	map {$_, &textdecode($dict{$_}, $encDefault)} (
	grep(exists($dict{$_}), ( '/Author', '/Creator', '/Title', '/Subject',
		'/Keywords', '/Producer')) )) ));
}

sub update_viewerpreferences { # fix /ViewerPreferences (pp557)
my ($idgen) = &list('/Root');
&error('ViewerPreferences', $idgen) unless ($idgen=~m/^$idgen_r(?:R)$/);
my ($type, @obj) = &content($idgen);
my $key = '/ViewerPreferences';
my %obj = @obj;
return( (exists($obj{$key})) ? ($idgen, &newobj('dict',
	&overwrite_dict(\@obj, '/ViewerPreferences', '<< >>'))) : ( ) );
}

sub update_outlines { # fix outlines (pp586).
my ($encDefault) = @_;
my (@outline) = &list('/Root/Outlines/FirstNext%%');
my @bin;
foreach my $outl (@outline) {
	my %act, my $title;
	my ($type, @obj) = &content($outl);
	my %obj = @obj;
	unless (exists($obj{'/A'}) && exists($obj{'/Title'})) {
		&debug('FOL:', join(',', keys(%obj)));
		next;
	}
	# change action to destination (pp647, pp581)
	my @new = ( );
	($type, %act) = &content($obj{'/A'});
	if ( #exists($act{'/Type'}) && '/Action' eq $act{'/Type'} &&
		exists($act{'/S'}) && '/GoToR' eq (&content($act{'/S'}))[1] &&
		exists($act{'/F'}) && "($fin)" eq
		&textdecode((&content($act{'/F'}))[1], $encDefault) ) {
		push(@new, '/A%', '/Dest', '/A', $act{'/D'});
		# if change key and value, use the old key.
	}
	push(@new, '/Title', &textdecode(
			(&content($obj{'/Title'}))[1], $encDefault));
	push(@bin, $outl, &newobj('dict', &overwrite_dict(\@obj, @new)));
}
return(@bin);
}

# PDF produced by "S22PDF V1.0 郭力(C) pdf@home.icm.ac.cn", or other tools
#	of China, occasionally show broken text and bookmarks.
#	These pdf use GB2312 for encoding in pages (but not bookmarks),
#	but the font is /TrueType without CMap and not embedded, making the
#	portibility poor.  The GB2312 is recorded as two octal back-slash
#	represent, like 中 (U+4E2D) -> 0xD6D0 (EUC-CN) -> \326\320, where
#	0xD6D0 (EUC-CN) == 0xA0A0 + 0x5448 (raw GB).  Raw GB2312 (0x0101 to
#	0x8794) plus 0xA0A0 becomes EUC-CN GB2312 (0xA1A1 to 0xF7FE).  When
#	the two bytes are interpreted separately, they are displayed as two
#	latin1 characters (not ASCII).
# --------------------------------
# evince_3.8.3-2_amd64: Evince
# AdbeRdr9.5.5-1_i386linux_enu (Adobe Reader 9): AdbeRdr9
# Adobe Acrobat X-10.0.0, Windows: AcrobatX
# Adobe Acrobat X-10.1.8, Windows: AcrobatX18
#	(AdbeRdr and Acrobat with 'Use local fonts' option off (I am not
#	testing the embedded fonts, thus the option should have no effect))
# ACRO_DISABLE_FONT_CONFIG (man1): not cache Font-config fonts,
#	may be in Cache/UnixFnt09.lst.
#		Evince		AdbeRdr9	AcrobatX	AcrobatX18
#		--------        --------	--------	--------
# TrueType (no CMap)                                                            
#  SimSun
#    Display	NoFL (*3)	NoFL		Perf		NoFL
#    Copy&Paste	Lat1		Lat1		Lat1		Lat1
#  #CB#CE#CC#E5, 宋体
#    Display	Lat1		NoFL		Perf		NoFL
#    Copy&Paste	Lat1		Lat1		Lat1		Lat1
# CIDFontType2
#  SimSun
#    Display	Perf		NoFC/Perf (*1)	Perf		Perf (*4)
#    Copy&Paste	Perf		Perf		Perf		Perf
#  #CB#CE#CC#E5, 宋体
#    Display	SubF		SubF (*2)	Perf		Perf (*4)
#    Copy&Paste	Perf		Perf		Perf		Perf
# --------------------------------
#	*1: AdbeRdr9 know fontname SimSun (by Cache/UnixFnt09.lst) but cannot
#		access fonts installed in Linux, giving up substitution and
#		complaining no Adobe Language Support Package.  If turn on
#		ACRO_DISABLE_FONT_CONFIG, then become Perf.
#	*2: AdbeRdr9 dunderstand fontnames #CB#CE#CC#E5 (宋体) and 黑体, and,
#		although it does not have the font, it finds substitutions
#		AdobeSongStd and AdobeHeitiStd.  But for 楷体, it complains
#		and gives up like in (*1).
#	*3: Evince gets correct fontnames, but interprets the string in PDF
#		as Latin1, and since somw fonts (KaiTi_GB2312) have shape for
#		Latin1, evince display black empty box or white space.
#	*4: Though SimSun and SimHei work, KaiTi_GB2312 and FangSong_GB2312
#		do not and are substituted by AdobeSongStd.  I guess Adobe
#		decides giving up supporting PDF with non-embbed CJK fonts,
#		at least not perfectly supporting. (old Acrobat shipped with
#		AdobeFangsongStd and AdobeKaitiStd, but AcrobatX not)
# --------------------------------
#	Perf: Perfect;
#	SubF: Substituted fonts.  Acroread and evince make font substitution
#		(guess a similar font), Acroread prefer use AdobeHeitiStd,
#		while evince prefer SimSun;
#	NoFC: No fonts for CJK texts, texts displayed as black solid point
#		(AdbeRdr9 and Acrobat) or as black empty box (Evince);
#	NoFL: No fonts and CJK texts are interpreted as Latin1 (1 character
#		as 2 letter);
#	Lat1: like trash code, but actually the two letters are the two bytes
#		for a EUC-CN GB2312 character.
# --------------------------------
# Acroread-9.5.5 guess fontname from /BaseFont in the CIDFontType2 font, e.g.,
#	mapping #CB#CE#CC#E5, Song, or Sung to AdobeSongStd-Light.otf.  
#	It understand quit a lot fontname (including wrong decoded GBK).
# Not perfect: the problem is acroread only using AdobeSongStd and
#	AdobeHeitiStd (OpenType) and abandoning system font (TrueType).
#	I still cannot configure aroread to access system font.
# I think using the name /SimSun etc is the best practice, dispite that doing
#	so does not actually change the font (only use another name), acroread
#	(Windows) displays totally correct; acroread (Linux) displays after
#	font substitution with ACRO_DISABLE_FONT_CONFIG set.
# Acroread X on Windows display pure TrueType (not CIDFontType2) of CJK
#	correctly, but the characters are copied and pasted as Latin1.
#	Interestingly, after the update to 10.1.8, the display are no longer
#	correct.  Now Acroread-10.1.8 and evince behave the same, complying to
#	the specilifcation of PDF.
sub update_font {
# fix pdf with TrueType in ANSI coding, which displayed incorrect in platforms
#	of non-GBK or no CJK fonts.  The TrueType is overwrite with
#	CIDTrueType with CIDMap coding
my ($font_templ, $fontdescriptor_h, %fontname) = @_;
#my (@f1) = &list('/Root/Pages/Kids%%/Resources/Font/%.*');
#my (@f2) = &list('/Root/Names/Dests/Kids%%/Names%%/Resources/Font/%.*');
#my (@f3) = &list('/Root/Pages/Kids%%/Resources/Font/%.*/DescendantFonts');
#my (@f4) = &list('/Font');
#my (@f5) = &list('Type/Font');
#print("@f3\n"); # @f1==@f2==@f4-@f3=@f5-@f3
my (@f1) = ( &list('/Root/Pages/Kids%%/Resources/Font/%.*'),
	&list('/Root/Pages/Resources/Font/%.*') );
my %fontdescriptor = %$fontdescriptor_h;
my @bin;
foreach my $f (@f1) {
	my ($type, %obj) = &content($f);
	next unless (exists($obj{'/Subtype'}) &&
		'/TrueType' eq $obj{'/Subtype'} &&
		exists($obj{'/Encoding'}) && 
		'/WinAnsiEncoding' eq $obj{'/Encoding'});
	unless (exists($obj{'/BaseFont'}) &&
		exists($fontname{$obj{'/BaseFont'}})) {
		&info("Unhandled font", $obj{'/BaseFont'});
		next;
	}
	my $name = $fontname{$obj{'/BaseFont'}};
	&info("Fix font", "$obj{'/BaseFont'}=>$name");
	my $font = $font_templ;
	$font=~s/\n/$eol/g;
	$font=~s|/%%BaseFont%%|/$name|g; # (name) not work
	# /BaseFont in /DescendantFonts really determine the font, and is this
	#	name shown in Attribute box of acroread.  acroread not use
	#	the one in /Type0 (though required, pp453), which is used by
	#	pdffont.
	my @fixfd = ( '/Type', '/FontDescriptor',
		'/FontName', "($name)"); # can be /name
	push(@fixfd, '/Flags', exists($fontdescriptor{Flags}{$name}) ?
		$fontdescriptor{Flags}{$name} : 4);
	push(@fixfd, '/Style', exists($fontdescriptor{Panose}{$name}) ?
		"<< /Panose $fontdescriptor{Panose}{$name} >>" : '<< >>');
	#$font=~s|/%%$_%%|$fontdescriptor{$_}{$name}|
	#	foreach (keys(%fontdescriptor));
	if (exists($obj{'/FontDescriptor'})) {
		my ($type, @fontdescriptor) = &content($obj{'/FontDescriptor'});
		@fixfd = &overwrite_dict(\@fontdescriptor, @fixfd);
	}
	my $fontdescriptor = &newobj('dict', @fixfd);
	$font=~s|/%%FontDescriptor%%|$fontdescriptor|;
	push(@bin, $f, $font);
}
return(@bin);
}

__END__

# below is the key steps of other approaches I tried to fix pdf, and all worked.

sub correct_file { # Not needed after I find the true bug.
	my ($fin) = @_;
	system("pdftk", $fin, qw\dump_data output data.txt\);
	my %encode = (InfoValue=>"cp936", BookmarkTitle=>"UCS-2BE");
	open(IN, "data.txt");
	my @line = readline(IN);
	chomp(@line);
	close(IN);
	open(OUT, ">FIX.data.txt");
	foreach my $line (@line) {
		if ($line=~m/^(InfoValue|BookmarkTitle): (.*)$/) {
			my ($key, $value) = ($1, $2);
			$line = "$key: " .&correct_line($value, $encode{$key});
		}
		print OUT (encode("UTF-8", "$line\n"));
	}
	close(OUT);
	system("pdftk", $fin, qw\update_info_utf8 FIX.data.txt output\,
		"FIX.$fin");
	return();
}

sub correct_line {
	my ($str, $encode) = @_;
	$str=~s/^&#255;&#254;//;
	# seems BOM for little-endian, though actual byte order is big-endian
	my %xmlentity = (quot=>'"');
	my %bit2to1 = (
		0x2022=>0x80, 0x2020=>0x81, 0x2021=>0x82, 0x2026=>0x83,
		0x2014=>0x84, 0x2013=>0x85, 0x0192=>0x86, 0x2044=>0x87,
		0x2039=>0x88, 0x203A=>0x89, 0x2212=>0x8A, 0x2030=>0x8B,
		0x201E=>0x8C, 0x201C=>0x8D, 0x201D=>0x8E, 0x2018=>0x8F,
		0x2019=>0x90, 0x201A=>0x91, 0x2122=>0x92, 0xFB01=>0x93,
		0xFB02=>0x94, 0x0141=>0x95, 0x0152=>0x96, 0x0160=>0x97,
		0x0178=>0x98, 0x017D=>0x99, 0x0131=>0x9A, 0x0142=>0x9B,
		0x0153=>0x9C, 0x0161=>0x9D, 0x017E=>0x9E, 0xFFFD=>0x9F,
		0x20AC=>0xA0,
		#0x5206=>0x5206, 0x5377=>0x5377, 0x56de=>0x56de,
		#0x5f55=>0x5f55, 0x76ee=>0x76ee, 0x8fd4=>0x8fd4,
	);
	# Despite the incorrect BOM, bookmark names in pdf is big-endian,
	#	but when pdftk decodes the names, it encryptes the byte with
	#	value between 0x80 to 0xA0.
	# Then I realize that if I only correct the BOM, then all bookmarks
	#	soon decoded automatically by pdf viewer.  Actually, there
	#	are several bookmarks with correct BOM, which are abtracted
	#	by pdftk as a 2-byte Unicode.
	my $len = length($str);
	my $newstr = '';
	for (my $i = 0; $len>$i; $i++) {
		my $entity;
		my $char = substr($str, $i, 1);
		if ('&' ne $char) {
			$newstr .= $char;
			next;
		}
		my $idx = index($str, ';', $i);
		if (-1==$idx) {
			die("!!Incorrect XML entity at $i: $str!");
		} else {
			$entity = substr($str, $i, $idx-$i+1);
			$i = $idx;
		}
		if ($entity=~m/^&#(.+);$/) {
			my $code = $1;
			if ($code=~m/^[0-9]+$/) {
				if (255<$code) {
					if (exists($bit2to1{$code})) {
						$code = $bit2to1{$code};
					} else {
						print("!!Unhandled: $code!\n");
						#$code = 0;
					}
				}
				$newstr .= pack(255<$code?'S>':'C', $code);
				# When $code falls in 0x80 to 0x9F, the
				#	encoding is ambiguous, need further
				#	decoding.
			} else {
				$newstr .= $xmlentity{$code};
			}
		} else {
			$newstr .= $entity;
		}
	}
	return(decode($encode, $newstr));
}
