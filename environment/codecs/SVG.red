Red [
	title:  "SVG (sickly vague graphics) codec"
	author: @hiiamboris
	needs:  [XML View]
	notes: {
	
	*	Status
	
		Decoder features supported or not:
		+ internal named resource inclusion (partial support)
		+ shapes supported by Draw
		+ simple text strings
		+ gradient and pattern pens
		- animations (no framework in the language anyway atm)
		- events (no Draw support, would require generating Spaces trees)
		- external resources (should we load them (files/urls)?)
		- CSS (needs CSS decoder, and compiler to apply it to the SVG tree)
		- scripting (needs JS or other interpreters)
		- namespaces (are just ignored)
		- forward references (spec recommends writing SVG for single pass decoders anyway)
		- validation (for simplicity assumes valid input)
		- colorspaces support (ICC color formats and properties)
		- named OS colors (need View support for them) - https://www.w3.org/TR/2008/REC-CSS2-20080411/ui.html#system-colors
		- text scaling, spacing, rotation and alignment by a path
		- filter effects (no Draw support)
		- clipping/masking (only viewport-based clipping atm, no paths)
		
		Encoder: not yet
		
		Decoder failure policy:
		- throw an error on unexpected input (e.g. broken XML format, mandatory SVG data missing)
		- warn and ignore unsupported SVG features (decoder extracts what it can)

	*	On inheritance...
		
		Inheritance in SVG is a monument to architectural waywardness:
		- they divide XML attributes into SVG "attributes" and SVG "properties" (aka presentation attributes)
		- sometimes attributes and properties share the same name (e.g. font-*) but not format or function,
		  and which one we're dealing with is only known from the current element name
		- attributes are not inherited, only properties
		- some properties are implicitly inherited deeply into all children, some are not
		- all properties can be explicitly inherited from the immediate parent when given "inherit" value
		- some elements can be referred to by internal or external URIs
		  they only inherit properties from their place of definition, not place of insertion
		  however they are also affected by some state (transforms, opacity, ...?) from their place of insertion
		- 'color' property may be referenced by color-related attributes in all (deep) children
		- 'opacity' property has to consider *all* its values up to the root of the tree, to compute its final value
		- 'transform' attribute must be ignored if it has an /svg namespace attached
		- 'x' and 'y' attributes of the topmost SVG in the file must be ignored, and not result in coordinate translation
		- some length units (including viewport dimensions) are relative to the viewport defined somewhere above
		- other length units are relative to the font size, which can also be relative to the above font size, etc.
		- gradients require their child elements (stops) to be emitted before gradients themselves can be emitted
		- text requires font knowledge, so all font-related parent attributes have to be finalized in order to emit text
		- there's also inheritance from CSS (and in CSS it is twisted from various sources of data), not supported yet
		- inheritance is not even properly documented, I had to gather these (not exhaustive) rules from around the spec :/
		  I'm dead sure none of the authors or SVG users understand how it all works together beyond obvious cases
		- see also pattern inheritance below...
		
		Minimal decoder workflow that enables this all:
		1. extract element attributes into a map for ease of access, filtering some out based on namespace
		2. replace "inherit" with the raw values from parent element (if any) - before decoding
		3. decode attributes into ready to use values (avoids multiple decoding later, replaces relative values with computed)
		4. do 1-8 for all children (recursively) - they will access decoded attributes of the parents
		5. emit 'transform' attribute since it has to precede all others
		6. emit other decoded attributes
		7. emit the element itself
		8. emit children after the element
		
		Controversies that SVG produces here are:
		- gradient elements require their child elements to be emitted first
		- text elements require their parent attributes to be computed first, making lengths absolute
		- inheritance (e.g. gradients referring to other gradients), ideally requires lengths not to be computed,
		  but inherited as percents and other relative units, for later computation at the place of their insertion
		This is an already conflicting set of constraints, unless we want to drown in special cases.
		Chromium sacrifices the latter condition and computes gradient lengths at their place of definition, which is a good tradeoff.
		
		Defaults for each element cannot be decoded until they are required, because there's no context otherwise.
		So decoding of defaults is done every time they are accessed.
		
		Each element's emitted Draw code is wrapped into a 'push' to prevent state spillage.
		
	*	On gradients...
		
		Gradients may be defined using relative units (%,em,ex) that depend on viewport or font-size properties.
		Are these units relative to the properties at the place of insertion, or at the place of definition?
		https://www.w3.org/TR/SVG11/pservers.html#LinearGradientElementHrefAttribute is vague, but likely means the latter.
		Browsers divide: Chromium computes size at place of definition, Firefox - at place of insertion.
		Former is closer to the spec, latter is more meaningful. What should we choose?
		
		GradientTransform can be expressed using Draw pen transforms after emitting the gradient.
		
		Opacity of each gradient color has to be modified at place of insertion.
		Any opacity at gradient's place of definition must be ignored, as well as transforms (experimental find).
		E.g. if gradient A was defined with opacity O(A) and gradient B with opacity O(B) and B inherits from A
		then when B is used as `fill` inside element with opacity O(F), effective opacity will be just O(F).
		  
		Gradient can inherit from any other gradient (including of different type),
		so it cannot be emitted at the place of definition without losing key/value structure required for inheritance.
		
	*	On patterns...
		
		As with gradient, relative units only depend on viewport & font-size at their place of definition, not insertion.
		
		These are trickier than gradients though: pattern can contain any other element.
		This includes other pattern and gradient definitions and application.
		
		PatternTransform can be expressed using Draw pen transforms after emitting the pattern.
		
		Pattern has two coordinate systems: one for its tile geometry (offset and size), another for content.
		Both CS can map either:
		- as (0,0)..(1,1) to the whole shape (0 to 100% of it) - not supported by Draw atm
		- directly to the current Draw CS - also not supported by Draw atm, unless shape starts at (0,0)
		
		Opacity of all colors within all elements within the pattern has to be deeply modified at place of insertion.  
		Any opacity at pattern's place of definition must be ignored, as well as transforms.
		Opacity propagates using the same rules as with gradients.
		
		Pattern can inherit from any other pattern. Experimentally found out that this includes:
		- pattern-specific attributes (not inheritable from parents), but not any inheritable properties
		  these are inherited as is, e.g. new pattern can redefine 'units' type, making all sizes invalid :/
		- content, that can be fully inherited if new pattern has no content, and here be dragons...

		Browsers disagree on how such inheritance should work, and the spec is completely silent.
		Example: pattern P1 with children C1 is inherited by empty pattern P2 which is then used in shape S3.
		Each has its own inherited font-size: F1 for P1+C1, F2 for P2 and F3 for S3.
		Both P1 and C1 sizes are expressed in 'em' units which are relative to 'font-size.
		In Chromium-based browsers, pattern P1 size is relative to F2, and children C3 size - to F1.
		In Firefox-based browsers, pattern P1 size is relative to F3, and children C3 size - to F1.
		And none of the options seems to make sense because it decouples pattern scale from its children.

	*	On units...		
	
		SVG supports units: (empty) % em ex px pt pc mm cm in
		Depending on DPI of a particular device, different parts of the same SVG may be scaled differently.
		So for proper "by design" rendering of SVGs we will need to expose DPI argument to the user.
		For now the codec is fully device-independent (assumes 96dpi). View will apply dpi scaling anyway.
		
	*	On font size...
		
		`font-size` property can be specified anywhere, there's no limitation.
		What should happen if one writes `... x="1em" font-size="20" y="1em" ...`?
		Of course, it never occurred to SVG designers that XML attributes have no order but decoding has.
		Chromium-based browsers apply whatever font-size they find before computing font-relative lengths.
		(so the result is like `font-size="20" x="1em" y="1em"`)
		Firefox-based browsers compute font-relative lengths first, then apply font-size to children only.
		(so the result is like `x="1em" y="1em" font-size="20"`)
		I don't know if it's even worth a special case in the codec.
		
		Another issue is font-size can be expressed in em/ex units, i.e. dependent on font-size above it.
		Or it can be expressed in % units, and depend on viewport (above or in the same element?).
		For simplicity I made font-size units always relative to upper scopes, ignoring current element.

	*	On paths...		
	
		:clap: https://www.w3.org/TR/SVG11/paths.html#PathDataClosePathCommand
		Funny how MIT/W3C heads try to save a few bytes on path syntax, effectively making humans do compression,
		while at the same time having gzip and wasting tons of bytes on XML (worst choice for structural data).
		So they decided that 'Z' command doesn't have to be followed by 'M' or 'm':
		in this case it should implicitly move to the absolute location where last 'M' or 'm' resulted (shape start)
		To support this 'feature' I have to manually track shape's starting offset ('start'),
		and since shape may start with 'm' (relative move), to support this relativity
		I also have to manually track where each command ends ('end'), making path decoding a mess.

	*	On text...
	
		This one is immensely complex.
		Even simple things like drawing a plain string at a specified offset require font metrics knowledge.
		Text origin specified in SVG for Latin script is located at font's baseline, while in Red it's above ascender line.
		So without precise metrics we can only roughly position the text vertically.
		Also the effect of such coordinate choice is that text from multiple scripts and of multiple font sizes in SVG
		will be automatically baseline-aligned, while we will have to split it on font changes and position separately.
		
		Text in SVG is structured as a tree, with each child affecting the next glyph offset, in parents as well.
		This requires measurement of every text string to track the offset.
		And that requires knowledge of the font at the time of measurement,
		so text can only be emitted after all of it's parents attributes are finalized,
		because font consists of various attributes which also depend on viewport and font size of parents.
		
		SVG allows to shift and rotate every isolated letter, which may make decoding extremely inefficient.
		Rendering of bidirectional text or top-down text will likely require manual positioning of every glyph too.
		
		Red also does not support separate pens for text fill and outline, while SVG does.
		Nor it supports aligning text along a predefined path.
		Finally SVG allows to define own glyphs and whole fonts using paths, as well as loading webfonts,
		and that all we'll unlikely be able to handle with any reasonable efficiency.
	}
];Red [


; #include %/d/devel/red/common/assert.red

; put system/codecs 'svg context [
put system/codecs 'svg make object! [
	title:     "SVG codec"
	name:      'SVG
	mime-type: [image/svg+xml]
	suffixes:  [%.svg %.svgz]
	
	encode: func [data [any-type!] where [none!]] [		;@@ how to use 'where'?
		cause-error 'internal 'feature-na []			;@@ TODO
	]
	
	;; block! 'data' allows one to manually decode the XML, and optionally compile CSS into it
	decode: function [
		"Decode SVG into a Draw block"
		data [string! binary! file! block!] "Original file contents or decoded XML in 'compact' format"
		/on canvas [pair! point2D!] "Initial viewport size (defaults to 100x100)"
	][
		if file?   data [
			data: apply 'read [data /binary %.svgz = suffix? data]
		]
		if binary? data [
			if find/match data #{1F8B} [data: decompress data 'gzip]	;-- 1F8B = gzip magic number
			data: to string! data
		]
		if string? data [data: load-xml/as data 'compact]
		
		data: internal/decode/:on data make [] 10 make #[] 20 canvas
		
		unless empty? data [
			data: compose/deep/only [
				push [(internal/init-draw) (data)]
			]
		]
		internal/font-cache: make map! 4				;-- reallocate cache to free resources
		data
	]
	
	verbose?: yes										;@@ turn it off when merging
	
	named-colors: #include %svg-colors.red

	internal: context [
	
	
		;; * * * * * * * * * * *
		;; *** HELPFUL FUNCS ***
		;; * * * * * * * * * * *
		
		
		warn: func [msg] [if verbose? [print rejoin msg]]		;@@ use #rejoin PR #5085
		
		fail-at: func [location [block! string!]] [
			cause-error 'script 'invalid-data reduce [location]
		]
		require: function [elem [word!] words [block!]] [
			foreach w words [unless get w [cause-error 'script 'no-arg [elem attr]]]
		]
		
		collect-set-words: function [code [block!]] [
			spec: spec-of function [] code
			parse spec [remove /local any change set w word! (to set-word! w)]
			spec
		]
		
		hide: function [code [block!]] [
			do with compose [(collect-set-words code) none] code
		]
		
		quiet: function [code [block!]] [						;@@ need language-wide mechanism for this
			old: verbose?
			set 'verbose? off
			also do code
			set 'verbose? old
		]
				
		clip: func [a [scalar!] b [scalar!] c [scalar!]] [		;@@ PR #5194
			min max a b max min a b c
		]
				
		len?: func [w [number!] h [number!]] [sqrt add w ** 2 h ** 2]
		rad?: func [p [point2D!]] [len? p/x p/y]
		sqrt2: sqrt 2
		
		;; since @dockimbel hates (x . y) and (x , y) notations, another one has to be creatively chosen ;)
		;; (L x y) seems ok: L looks as XY coordinate axes pointing up and right, and a very unlikely name for a variable
		; .: make op! :as-point2D
		L: :as-point2D
		
		ignore: func [x] [[]]
		only:   func [x] [any [:x []]]
		
		into: func [buffer [block!] data [block!]] [compose/deep/into data tail buffer]
		
		with: func [ctx [any-object! function! any-word! block!] code [block!]] [
			case [
				not block? :ctx  [bind code :ctx]
				set-word? :ctx/1 [bind code context ctx]
				'otherwise       [foreach ctx ctx [bind code do :ctx]  code]
			]
		]
		
		load-token: func [start [string!] end [string!]] [
			transcode/one/part start offset? start end	;@@ https://github.com/red/red/issues/4106#issuecomment-546711381
		]
		
		alpha-blend: function [color [tuple!] opacity [number!]] [
			color: color + 0.0.0.0
			color/4: round/to 255 - (255 - color/4 * opacity) 1
			color
		]
		
		#assert [
			200.100.0.128 = alpha-blend 200.100.0 50%
			200.100.0.236 = alpha-blend 200.100.0.192 30%
		]
		
		
		
		;; * * * * * * * *
		;; *** GRAMMAR ***
		;; * * * * * * * *
		
	
		?!: [p: (?? p)]											;-- debugging tool
		sign!:				charset "+-"
		dd!:				charset [#"0" - #"9"]				;-- Decimal Digit
		alpha!:				charset [#"a" - #"z" #"A" - #"Z"]
		hex-digit!:			charset [#"a" - #"f" #"A" - #"F" #"0" - #"9"]
		white!:				charset [9 10 13 32]				;-- https://www.w3.org/TR/SVG11/types.html <list-of-Ts>
		ws-or-comma!:		union white! charset ","
		ws*:				[any white!]
		ws+:				[some white!]
		wsc*:				[any ws-or-comma!]
		wsc+:				[some ws-or-comma!]
		;; numbers have to be validated for security of 'transcode/one', so they have a complete syntax
		=basic-number=:		[opt sign! [some dd! opt #"." any dd! | #"." some dd!]]
		=exponent=:			[#"e" opt sign! some dd!]
		=unsafe-number=:	[=basic-number= opt [#"e" opt sign! some dd!]]
		=number=:			[=unsafe-number= ahead [end | ws-or-comma! | ")"]]
		=any-number=:		[=basic-number= opt [#"%" | =exponent=] ahead [end | ws-or-comma! | ")"]]
	
		reset-draw: compose [							;-- used to explicitly reset Draw state inside pattern pens
			pen 0.0.0 fill-pen off
			anti-alias on font (make font! [])
			line-width 1 line-join miter line-cap flat
		]

		init-draw: [pen off fill-pen 0.0.0]				;-- https://www.w3.org/TR/SVG11/propidx.html
		
		;@@ let user control dpi value via argument, scale units appropriately
		units: make map! [								;-- fixed units for lengths, except %/em/ex
			""   1.0
			"px" 1.0
 			"pt" 1.333333333333333						;-- 1 point = 1/12 pica
			"pc" 16.0									;-- 1 pica = 1/6 inch
			"mm" 3.779527559055118
			"cm" 37.79527559055118						;-- 1 cm = 1/2.54 inch
			"in" 96.0
		]
		
		;; percent unit is applied differently to different attributes, so 3 categories here: X, Y (fixed set) and XY (fallback)
		;@@ to be expanded based on https://www.w3.org/TR/SVG11/attindex.html
		length-types: #[
			#x x #x1 x #x2 x #cx x #dx x #fx x #rx x #refx x #width  x #markerwidth  x
			#y y #y1 y #y2 y #cy y #dy y #fy y #ry y #refy y #height y #markerheight y
		]
		
		length-type?: func [attr [issue!]] [
			any [length-types/:attr 'xy]
		]
		
		;; attribute types that use scales from the stack
		relative:		make hash! [length lengths? #(true)] 
		
		;; elements that are not emitted and whose children are never emitted, but an #id may be assigned
		ignored:		make hash! [defs pattern linearGradient radialGradient #(true)]
		
		;; elements that accept 'transform's - https://www.w3.org/TR/SVG11/attindex.html
		transforming:	make hash! [defs g circle ellipse rect line path polygon polyline #(true)]	;@@ to be extended
		
		;; elements that establish a new viewport (and support viewBox) - https://www.w3.org/TR/SVG11/attindex.html
		deforming:		make hash! [svg pattern #(true)]		;@@ to be extended
		
		;; elements that do not require a 'push []' wrapper
		flat:			make hash! [stop #(true)]
		
		;; elements that emit 'text' draw commands (in all other elements text is ignored)
		textual:		make hash! [text tspan #(true)]
		
		;; defaults must be strings - cannot be decoded without context (e.g. 100% has no meaning in a vacuum)
		defaults: #[
			all #[										;-- applies to all SVG elements
				;; specials
				content				[]					;-- used by gradients/patterns flattening
				font				#(none)				;-- reassigned below
				viewport			(100,100)			;-- arbitrary, to avoid errors ;@@ should be user-provided
				#font-size			"12"				;-- ditto, reassigned below
				
				;; https://www.w3.org/TR/SVG11/propidx.html - selected property defaults, to be extended once more are supported
				#color				"black"				;-- reassigned below
				#fill				"black"
				#fill-opacity		"1"
				#fill-rule			"nonzero"
				#opacity			"1"					;-- affects pen, fill, gradient stops
				#stop-color			"black"
				#stop-opacity		"1"
				#stroke				"none"
				#stroke-linecap		"butt"
				#stroke-linejoin	"miter"
				#stroke-opacity		"1"
				#stroke-width		"1"
				#text-anchor		"start"
				#direction			"ltr"
				#text-decoration	"none"
			
				;; https://www.w3.org/TR/SVG11/attindex.html - attribute defaults are buried deep in the docs and depend on the element
				#transform			""
				#preserveAspectRatio "xMidYMid meet"	;-- https://www.w3.org/TR/SVG11/coords.html#PreserveAspectRatioAttribute
			]
			svg		#[#x  "0" #y  "0" #width "100%" #height "100%" #baseProfile "none"]
			use		#[#x  "0" #y  "0"]
			line	#[#x1 "0" #y1 "0" #x2 "0" #y2 "0"]
			rect	#[#x  "0" #y  "0"]					;-- 'rx' and 'ry' need special logic
			circle	#[#cx "0" #cy "0"]
			ellipse	#[#cx "0" #cy "0"]
			radialGradient #[
				#cx "50%" #cy "50%" #r "50%" #spreadMethod "pad"
				#gradientTransform "" #gradientUnits "objectBoundingBox"	;-- 'fx' and 'fy' need special logic
			]
			linearGradient #[
				#x1 "0%" #y1 "0%" #x2 "100%" #y2 "0%" #spreadMethod "pad"
				#gradientTransform "" #gradientUnits "objectBoundingBox"
			]
			pattern #[
				#x "0" #y "0" #width "0" #height "0" #patternTransform ""
				#patternUnits "objectBoundingBox" #patternContentUnits "userSpaceOnUse"
			]
			text  #[#x "0" #y "0"]; #dx "" #dy "" #rotate "")
			tspan #[#x "0" #y "0"]
		]
		;; it's up to us to decide starting color, so OS pen color makes most sense
		attempt [put defaults/all #color rejoin ["#" enbase/base to binary! system/view/metrics/colors/text 16]]
		;; for font we can use system default size
		put defaults/all #font-size form any [attempt [system/view/fonts/size] 12]
		;; default Draw font
		defaults/all/font: make font! []
		
		;; to some upper attributes/properties I need access from any depth:
		;; for 'opacity' I need to know all the values in the stack, for others - only the last explicit value
		deep-attrs: make hash! [
			#fill-opacity #stroke-opacity				;-- used to apply opacity when fill/stroke value changes
			#stop-opacity								;-- used when when forming gradient stops
			#font-size #x-height						;-- used to measure em/ex unit size, and to construct font
			#font-family #font-weight #font-style		;-- used to construct font object
			#text-anchor #text-decoration #direction	;-- affect every child 'text' emitted
			#color										;-- used to give value to pen='currentColor'
			viewport									;-- used to scale percent unit
			font										;-- used to measure text spans
			#(true)										;-- this just simplifies lookup by enabling paths
		]
		
		;; this is used upon pen emission, assumes that map contains viewport and #font-size - must be set
		maybe-get-from-map: function [map [map!] attr [issue! word!]] [
			any [
				map/:attr
				if default: any [
					select defaults/(map/element) attr
					defaults/all/:attr
				][
					decode-attr default tail reduce [map] attr
				]
			]
		]
		
		;@@ get rid of elem-name, use stack/-1/element
		maybe-get-value: function [stack [block!] attr [issue! word!] /for elem-name [word!]] [
			any [
				either deep-attrs/:attr [
					pos: stack
					while [not head? pos] [						;@@ use for-each/reverse
						pos: back pos
						if value: pos/1/:attr [break]
					]
					value
				][
					stack/-1/:attr
				]
				if default: any [
					if for [select defaults/:elem-name attr]
					defaults/all/:attr
				][
					if string? default [default: decode-attr default stack attr]
					default
				]
			]
		]
		
		get-value: function [stack [block!] attr [issue! word!] /for elem-name [word!]] [
			any [
				maybe-get-value/:for stack attr elem-name
				cause-error 'script 'no-arg [any [elem-name if stack/-1 [stack/-1/element]] attr]
			]
		]
		
		get-total-opacity: function [stack [block!]] [
			opacity: 1.0
			foreach elem head stack [							;@@ use fold/accumulate + map-each
				opacity: opacity * any [elem/#opacity 1]
			]
			opacity
		]
		
		fetch-url: function [url [string!] dict [map!]] [		;@@ only supports internal URLs for now
			any [
				all [url/1 = #"#" dict/(next url)]
				also none warn ["Unknown resource ID: " url]
			]
		]
		
		from: make op! function [string [string!] options [map!]] [
			any [options/:string  fail-at string]
		]
		
		;; decoders have 3 arguments: string [string!] and optional stack [block!] and attr [issue! word!]
		;; stack is required by font-size which has to be inherited always as computed value
		;;   so font-size has to become a final number at decoding stage
		;; same for viewport: since content is emitted before parents, content needs access to final viewport size
		;;   but viewport cannot be handled here because it's not a single attribute but a mess
		;; attr is required by lengths where final value depends on element name
		decoders: make map! [
			units		[string from #["userSpaceOnUse" user "objectBoundingBox" object]]
			spread		[string from #["reflect" reflect "repeat" repeat "pad" pad]]
			linecap		[string from #["butt" flat "square" square "round" round]]
			;; https://www.w3.org/TR/SVG11/painting.html#StrokeProperties
			;; spec says default miter-limit is 4x so "miter" in SVG => miter-bevel in Draw:
			linejoin	[string from #["round" round "bevel" bevel "miter" miter-bevel]]
			transform	[decode-transform   string]
			aspect		[decode-aspect      string]
			color		[decode-color       string stack]
			numbers		[decode-numbers     string]
			length		[decode-length      string stack attr]	;-- integer/float + unit/percent
			lengths?	[decode-lengths*    string stack attr]	;-- single or multiple: integer/float + unit/percent, depends on element
			number		[decode-number      string]				;-- integer, float or percent
			points		[decode-points      string]				;-- int/float couples to convert to point2Ds
			percentage	[clip 0 1 decode-number string]			;-- spec prescribes clipping of opacities and gradient offsets
			path		[decode-path        string] 
			font-size	[decode-font-size   string stack]
			font-family	[decode-font-family string]
			font-weight	[string from font-weights]
			font-style	[string from #["normal" normal "italic" italic "oblique" oblique]]
			text-anchor	[string from #["start" 0.0 "middle" 0.5 "end" 1.0]]
			text-dir	[string from #["ltr" right "rtl" left]]
			text-deco	[string from #["none" none "underline" underline "overline" overline "line-through" strike "blink" blink]]
		]
		hide [
			foreach [type body] decoders [				;@@ use map-each
				decoders/:type: function [string stack attr] body
			]
		]
		
		attr-types: #[
			;; #x/y/dx/dy have conflicting syntaxes: multiple lengths in <text>, single in shapes
			#x lengths? #y lengths? #dx lengths? #dy lengths?
			#x1 length #x2 length #cx length #fx length #rx length #refx length #width  length #markerwidth  length
			#y1 length #y2 length #cy length #fy length #ry length #refy length #height length #markerheight length
			#z length #r length		;@@ lot more to add...
			#rotate					numbers
			#stroke-width			length
			#stroke-linecap			linecap
			#stroke-linejoin		linejoin
			#color					color
			#stroke					color
			#fill					color
			#opacity				percentage
			#stroke-opacity			percentage
			#fill-opacity			percentage
			#gradientUnits			units
			#patternUnits			units
			#patternContentUnits	units
			#gradientTransform		transform
			#patternTransform		transform
			#spreadMethod			spread
			#offset					percentage			;-- gradient stop, clipped: https://www.w3.org/TR/SVG11/pservers.html#StopColorProperty
			#stop-opacity			percentage
			#stop-color				color
			#viewBox				points
			#preserveAspectRatio	aspect
			#transform				transform
			#d						path				;-- path dialect
			#points					points				;-- polygon, line, etc.
			#font-size				font-size
			#font-family			font-family
			#font-weight			font-weight
			#font-style				font-style
			#text-anchor			text-anchor
			#direction				text-dir
			#text-decoration		text-deco
		]
		
		decode-attr: func [string [string!] stack [block!] attr [issue!]] [
			decoder: any [:decoders/(attr-types/:attr) :return]	;-- return = fallback to no decoding
			decoder string stack attr
		]
		
		;; see the header: font-size has to be decoded before the rest, since lengths may need to use it
		;; color has to be decoded first too, because pens in the same element may refer to it as 'currentColor'
		ordered: make hash! [#font-size #color] 
		
		decode-attributes: function [
			"Decode all of the element's attributes into Red values"
			stack [block!]
		][
			list: make hash! keys-of scope: stack/-1
			list: difference ordered difference list ordered	;-- enforce order
			foreach attr list [									;@@ use map-each to filter attrs
				if issue? attr [scope/:attr: decode-attr scope/:attr stack attr]
			]                                                               
			;; font depends on multiple attributes and so needs assembly after decoding
			unless empty? intersect keys-of scope [
				#font-size #font-family #font-weight #font-style
			] [scope/font: make-font stack]
			if deforming/(scope/element) [				;@@ what if it has no geometry attached?
				scope/viewport: compute-viewport stack
			]
		]

		
		
		decode-number: function [string [string!]] [	;-- for single-number values only
			parse string [wsc* =any-number= wsc* end | (fail-at string)]
			transcode/one string
		]
		
		#assert [
			1   = decode-number "1. "
			0.1 = decode-number ".1 "
			1   = decode-number "1.0e-0"
			0.1 = decode-number " 10%, "
			error? try [decode-number "10e1%"]
			error? try [decode-number "1.0."]
		]
		
		decode-numbers: function [string [string!]] [	;-- for number lists: no percent support here, no errors
			parse string [wsc* collect some [s: =number= e: wsc* keep (load-token s e)]]
		]
		
		#assert [
			[1 2 3] = decode-numbers "1 2 3"
			[1 2 3] = decode-numbers " 1.0,0.2e1, 3) "
		]
		
		compute-length: function [number [string!] unit [string!] end [string!] stack [block!] attr [issue!]] [
			scope: stack/-1
			value: load-token number unit
			unless tail? end [unit: copy/part unit end]	;-- trailing whitespace must be ignored
			scale: any [
				units/:unit
				switch unit [
					"%" [
						viewport: get-value/for stack 'viewport scope/element
						0.01 * switch type: length-type? attr [
							x y [viewport/:type]
							xy  [divide rad? viewport sqrt2]	;-- https://www.w3.org/TR/SVG11/coords.html#Units
						]
					]
					;@@ "ex" requires "x-height" font metric ideally (or attribute support), right now works like IE
					"em" "ex" [
						font-size: get-value/for stack #font-size scope/element
						font-size / pick [1 2] "em" = unit
					]
				]
				fail-at number
			]
			scale * value
		]
		
		decode-length: function [string [string!] stack [block!] attr [issue!]] [	;-- number with unit
			parse string [
				wsc* number: =unsafe-number= unit: [to white! | to end] end:
			|	p: (fail-at p)
			]
			compute-length number unit end stack attr
		]
		
		#assert [
			0  = decode-length "0"       tail [#[element: svg viewport: (30,20) #font-size 10]] #x
			1  = decode-length "1"       tail [#[element: svg viewport: (30,20) #font-size 10]] #x
			1  = decode-length "1px"     tail [#[element: svg viewport: (30,20) #font-size 10]] #x
			1  = decode-length "1.0px"   tail [#[element: svg viewport: (30,20) #font-size 10]] #x
			32 = decode-length " 2.0pc " tail [#[element: svg viewport: (30,20) #font-size 10]] #x
			96 = decode-length "1in"     tail [#[element: svg viewport: (30,20) #font-size 10]] #x
			3  = decode-length "10%"     tail [#[element: svg viewport: (30,20) #font-size 10]] #x
			2  = decode-length "10%"     tail [#[element: svg viewport: (30,20) #font-size 10]] #y
			5  = decode-length "0.5em"   tail [#[element: svg viewport: (30,20) #font-size 10]] #x
			3  = decode-length "10%"     tail [#[element: svg viewport: (30,30) #font-size 10]] #xy
		]
		
		decode-lengths: function [string [string!] stack [block!] attr [issue!]] [	;-- zero or more numbers with units
			parse string [wsc* collect any [
				number: =unsafe-number= unit: [to white! | to end] end: wsc*
				keep (compute-length number unit end stack attr)
			|	end | (p: fail-at p)					;@@ or ignore invalid trail?
			]]
		]
		
		#assert [
			[3 1] = decode-lengths "10% 1px" tail [#[element: svg viewport: (30,20)]] #x
		]
		
		;; workaround for #x and #y attributes having different formats across elements
		decode-lengths*: function [string [string!] stack [block!] attr [issue!]] [
			element: all [scope: stack/-1  scope/element]
			decoder: either textual/:element [:decode-lengths][:decode-length]
			decoder string stack attr
		]
		
		;; returns: tuple!, 'off, string! (gradient/pattern #id), or none if failed to decode
		decode-color: function [string [string!] stack [block!]] [
			parse string [
				"none" end (color: 'off)
			|	"currentColor" end (color: get-value stack #color)
			|	"rgb(" (buf: clear []) 3 [				;-- rgb(1,2,3) or rgb(1%,2%,3%)
					ws* s: =basic-number= e: (n: load-token s e)
					opt ["%" (n: n * 2.55)] opt "," (append buf n)
				] ws* ")" (color: to tuple! buf)
			|	"#" 1 2 [3 hex-digit!] end (			;-- #def or #ddeeff
					color: hex-to-rgb transcode/one string
				)
			|	"url(" ws* copy color to [#")" | white!] thru #")"	;-- url(#myGradient) etc - needs dict access
				;@@ next (fallback) color is ignored atm, but should be used
			|	some alpha! (							;-- 'aqua' etc
					color: named-colors/:string
					;@@ add support for OS colors https://www.w3.org/TR/2008/REC-CSS2-20080411/ui.html#system-colors
				)
			]
			unless color [warn ["Unsupported color '"string"' is ignored"]]
			color
		]
		
		#assert [
			255.255.255 = decode-color "#FfF"         tail [#[#color 2.3.4]]
			255.255.255 = decode-color "#fFFffF"      tail [#[#color 2.3.4]]
			1.2.3       = decode-color "rgb(1,2,3)"   tail [#[#color 2.3.4]]
			0.0.0       = decode-color "black"        tail [#[#color 2.3.4]]
			'off        = decode-color "none"         tail [#[#color 2.3.4]]
			2.3.4       = decode-color "currentColor" tail [#[#color 2.3.4]]
			"#ref"      = decode-color "url(#ref)"    tail [#[#color 2.3.4]]
		]
		
		;; https://www.w3.org/TR/SVG11/implnote.html#ErrorProcessing prescribes to:
		;; "render the ‘polyline’ or ‘polygon’ up to the segment [in 'points'] with the error" 
		;; SVG 2.0 says in https://www.w3.org/TR/SVG/shapes.html:
		;; "In such error cases the user agent will drop the last, odd coordinate and otherwise render the shape"
		;; also, specs don't mention it, but "100-200" is a valid (100, -200) point in polylines
		;; as evidenced by (approved) test %shapes-grammar-01-f.svg and browsers decoding it fine
		decode-points: function [string [string!]] [
			parse string [
				collect any [
					wsc* x: =unsafe-number= xe: wsc* y: =unsafe-number= ye:
					keep (as-point2D load-token x xe load-token y ye)
				] wsc*
				;; warn but accept any invalid trailing data
				[end | p: (warn ["Invalid 'points' data at: "mold/part p 100])]
			]
		]
		
		#assert [
			[]             = decode-points {}
			[(1,2)]        = decode-points {1, 2}
			[(1,2)  (3,4)] = decode-points { 1 , 2 3,4 }
			[(10,2) (3,4)] = decode-points { 1e1,2,3e+0 4e-0}
			[(10,2) (3,4)] = quiet [decode-points { 1e1,2,3e+0 4e-0zomg}]
		]
		
		path-grammar: [
			=flag=:       [set flag [#"0" | #"1"] wsc* (flag: flag = #"1")]
			=large=:      [=flag= (large?: pick [large []] flag)]
			=sweep=:      [=flag= (sweep?: pick [large []] flag)]
			=num=:        [s: =unsafe-number= e: wsc* (num: load-token s e)]
			=x=:          [=num= (x:   num)]
			=y=:          [=num= (y:   num)]
			=rot=:        [=num= (rot: num)]
			=xy=:         [=x= =y= (xy:  as-point2D x y)]
			=xy1=:        [=x= =y= (xy1: as-point2D x y)]
			=xy2=:        [=x= =y= (xy2: as-point2D x y)]
			=rad=:        [=x= =y= (rad: as-point2D x y)]
			=switch-cmd=: [(=scan+emit=: path-command-args/:cmd)]
			cmd:          none
		]
		;; auto collect all set-words into a context
		do bind path-grammar path-grammar: context append sort collect-set-words path-grammar 'none
		
		;; note: SVG paths do not support units (incl. %), only attributes
		path-command!: charset "MmLlZzHhVvCcSsQqTtAa" 
		
		;; https://www.w3.org/TR/SVG11/implnote.html#ErrorProcessing prescribes to:
		;; "render the ‘path’ up to the point of the path data error"
		;; see also https://www.w3.org/TR/SVG11/implnote.html#PathElementImplementationNotes
		decode-path: function [string [string!] /extern cmd] with path-grammar [
			buffer: make [] (length? string) / 4
			end: start: (0,0)
			cmd: #"L"									;@@ arbitrary; should it be an error instead?
			parse/case string [
				any [
					wsc*
					opt [[
						#"M" ws* =xy= (cmd: #"L" into buffer [move  (xy)] start: end: xy)	;-- next command after M is implicitly L
					|	#"m" ws* =xy= (cmd: #"l" into buffer ['move (xy)] start: end: end + xy)
					] =switch-cmd=]
					any [opt [set cmd path-command! ws* =switch-cmd=] =scan+emit=]
				] wsc*
				[end | p: (warn ["Invalid 'path' data at: "mold/part p 100])]
			]
			buffer
		]
		
		;; see header notes on complexities involved here;
		;; 'start' is a shape's starting offset, 'end' last command's closing offset (where it leaves the pen)
		path-command-args: make map! with [path-grammar :decode-path] [
			#"L" [ =xy= (into buffer [line  (xy)] end: xy) ]
			#"l" [ =xy= (into buffer ['line (xy)] end: end + xy) ]
			#"Z" [ (into buffer [close move (end: start)]) ]	;-- if no M after Z, location is reset to last start
			#"z" [ (into buffer [close move (end: start)]) ]
			#"H" [ =num= (into buffer [hline  (num)] end/x: num) ]
			#"h" [ =num= (into buffer ['hline (num)] end/x: end/x + num) ]
			#"V" [ =num= (into buffer [vline  (num)] end/y: num) ]
			#"v" [ =num= (into buffer ['vline (num)] end/y: end/y + num) ]
			#"C" [ =xy1= =xy2= =xy= (into buffer [curve  (xy1) (xy2) (xy)] end: xy) ]
			#"c" [ =xy1= =xy2= =xy= (into buffer ['curve (xy1) (xy2) (xy)] end: end + xy) ]
			#"S" [ =xy2= =xy= (into buffer [curv  (xy2) (xy)] end: xy) ]
			#"s" [ =xy2= =xy= (into buffer ['curv (xy2) (xy)] end: end + xy) ]
			#"Q" [ =xy1= =xy= (into buffer [qcurve  (xy1) (xy)] end: xy) ]
			#"q" [ =xy1= =xy= (into buffer ['qcurve (xy1) (xy)] end: end + xy) ]
			#"T" [ =xy= (into buffer [qcurv  (xy)] end: xy) ]
			#"t" [ =xy= (into buffer ['qcurv (xy)] end: end + xy) ]
			#"A" [ =rad= =rot= =large= =sweep= =xy=
			       (into buffer [arc  (xy) (rad/x) (rad/y) (rot) (sweep?) (large?)] end: xy) ]
			#"a" [ =rad= =rot= =large= =sweep= =xy=
			       (into buffer ['arc (xy) (rad/x) (rad/y) (rot) (sweep?) (large?)] end: end + xy) ]
		]
		
		#assert [
			[]                          = decode-path {}
			[move (1, 2)]               = decode-path {M 1, 2}
			['move (1, 2) 'line (3, 4)] = decode-path {m 1 , 2 3,4 }	;-- https://www.w3.org/TR/SVG11/paths.html#PathDataMovetoCommands
			[move (10, 2) line (3, 4)]  = decode-path {M 1e1,2,3e+0 4e-0}
			[move (1, 2)  line (3, 4) close move (1, 2) line (5, 6)]
										= decode-path {M1 2 3 4zL5 6}	;-- https://www.w3.org/TR/SVG11/paths.html#PathDataClosePathCommand
			[move (100, -200)]          = decode-path {M100-200}		;-- https://www.w3.org/TR/SVG11/paths.html#PathDataBNF
			[move (0.6, 0.5)]           = decode-path {M 0.6.5}			;-- yes, this idiocy is by design
			[move (10, 2) line (3, 4)]  = quiet [decode-path {M 1e1,2,3e+0 4e-0error}]
		]
		
		shift-factors: #[
			none		#(none)
			XMinYMin	(0.0, 0.0)
			XMidYMin	(0.5, 0.0)
			XMaxYMin	(1.0, 0.0)
			XMinYMid	(0.0, 0.5)
			XMidYMid	(0.5, 0.5)
			XMaxYMid	(1.0, 0.5)
			XMinYMax	(0.0, 1.0)
			XMidYMax	(0.5, 1.0)
			XMaxYMax	(1.0, 1.0)
		]
		
		decode-aspect: function [string [string!] /local slice?] [	;-- returns: [shift-factor(point/none) fit?(logic)]
			parse string [
				opt ["defer" ws+]						;@@ will be used by <image> referring to external svgs
				s: some alpha! e: (shift: select shift-factors load-token s e)
				opt [ws+ ["meet" | set slice? "slice"]] 
			|	p: (fail-at p)
			]
			reduce [shift not slice?]
		]
		
		#assert [
			[#(none)  #(true) ] = decode-aspect "none"
			[(1, 0)   #(true) ] = decode-aspect "xMaxYMin meet"
			[(0, 0.5) #(false)] = decode-aspect "xMinYMid slice"
		]
		
		decode-transform: function [string [string!] /local cmd] [
			buffer: make [] (length? string) / 3
			parse string [ws* any [
				p: copy cmd some alpha! ws* "(" s: to ")" e: skip ws*
				(
					nums: decode-numbers s e
					into buffer any [transforms/:cmd  fail-at p]
				)
			|	end | (fail-at p)
			]]
			buffer
		]
		
		transforms: make map! with :decode-transform [
			"matrix"	[matrix [(nums)]]
			"translate"	[translate (as-point2D nums/1 any [nums/2 0])]
			"scale"		[scale (nums/1) (any [nums/2 nums/1])]
			"rotate"	[rotate (nums/1) (as-point2D any [nums/2 0] any [nums/3 0])]
			"skewY"		[skew (nums/1) 0.0]
			"skewY"		[skew 0.0 (nums/1)]
		]
		
		specialize-transform: function [block [block!] "copied" pen [word!]] [	;-- converts into pen/fill-pen transform
			pen: to lit-word! pen
			parse block: copy block [any [word! insert (pen) | skip]]
			block
		]
		
		#assert [
			[]                     = decode-transform ""
			[translate (-10, -20)] = decode-transform "translate(-10,-20)"
			[scale 2 2]            = decode-transform "scale(2)"
			[rotate 45 (0,0)]      = decode-transform "rotate(45)"
			[translate (-10, -20) scale 2 2 rotate 45 (0,0) translate (5, 10)]
			= decode-transform "translate(-10,-20) scale(2) rotate(45) translate(5,10)"
			[translate 'fill-pen (-10, -20) scale 'fill-pen 2 2]
			= specialize-transform decode-transform "translate(-10,-20) scale(2)" 'fill-pen
		]
		
		;; https://www.w3.org/TR/2008/REC-CSS2-20080411/fonts.html#value-def-absolute-size
		;; "On a computer screen a scaling factor of 1.2 is suggested between adjacent indexes"
		font-sizes: make map! compose with :system/view/fonts [
			"xx-small"	(size / 1.728)
			"x-small"	(size / 1.44)
			"small"		(size / 1.2)
			"medium"	(size)							;@@ or use a predefined 12px for 'medium'?
			"large"		(size * 1.2)
			"x-large"	(size * 1.44)
			"xx-large"	(size * 1.728)
		]
		
		;; this has to take scales from the parent element(s), not the current one
		;; else font-size of "2em" will cyclically depend on itself
		;; returned size is line-height size in pixels, not Red font size (necessary for em/ex lengths)
		decode-font-size: function [string [string!] stack [block!]] [
			any [
				font-sizes/:string
				if op: switch string ["larger" [:*] "smaller" [:/]] [
					(get-value back stack #font-size) op 1.2
				]
				decode-length string back stack #font-size
			]
		]
		
		generic-fonts: #[
			"serif"			serif
			"sans-serif"	sans-serif
			"cursive"		serif
			"fantasy"		serif
			"monospace"		fixed
		]
			
		;@@ without REP #139 there's no way to know if given font is supported,
		;@@ so we can only blindly choose the first of given alternatives and hope for the best
		decode-font-family: function [string [string!] /local name] [
			parse string [ws* copy name [to #"," | to end]]		;@@ grammar is unknown
			trim name
			if #"'" = first name [take name]					;@@ use 'trim/with' if /with becomes sane
			if #"'" = last  name [take/last name]
			if generic: generic-fonts/:name [
				name: system/view/fonts/:generic
			]
			name
		]
		
		;; numbers come from a set, so I wonder what those trailing zeroes are for :/
		font-weights: #[
			"normal"	normal
			"bold"		bold
			"bolder"	bold
			"lighter"	normal
			"100"		normal
			"200"		normal
			"300"		normal
			"400"		normal
			"500"		normal
			"600"		bold
			"700"		bold							;-- normative weight for 'bold' is 700
			"800"		bold
			"900"		bold
		]
		
		compute-viewport: function [stack [block!]] [
			scope: stack/-1
			foreach [word attr] [w: #width h: #height] [
				set word get-value/for stack attr scope/element
			]
			box: scope/#viewBox
			src-size: if box [box/2]
			tgt-size: as-point2D w h
			any [src-size tgt-size]
		]
		
		
		
		;; * * * * * * * * * * *
		;; *** DRAW EMITTERS ***
		;; * * * * * * * * * * *
		
		
		apply-opacity: function [block [block!] opacity [number!] /deep] [
			if opacity < 1 [
				else: pick [ [ahead block! into rule | skip] [skip] ] deep
				parse block: copy/:deep block rule: [any [
					change set color tuple! (alpha-blend color opacity)
				|	else
				]] 
			]
			block
		]
		
		#assert [
			[push [pen 200.100.0.236]] = apply-opacity/deep [push [pen 200.100.0.192]] 30%
		]
		
		;; see the header on all the intricacies involved here for gradients and patterns
		;; in short, must emit a map (to be able to combine it),
		;; then later apply opacity and specialize pen transform (for patterns - deeply affects all colors)
		;; pattern content can be emitted as /content, because pattern always enforces a viewport
		;@@ TODO: decide at what point to compute gradient/pattern lengths (see the header notes)
		flatten-pen: function [stack [block!] dict [map!] type [word!]] [
			scope: stack/-1
			unless scope/#id [exit]						;-- gradient without id cannot be used, so ignore it
			if scope/#href [							;-- inherit attrs from referenced gradient
				ref: fetch-url scope/#href dict
				all [ref  not map? :ref/1  fail-at ref]
			]
			either ref [
				map: extend copy ref: ref/1 scope
				if all [empty? map/content not empty? ref/content] [	;-- do not override non-empty stops with empty
					map/content: ref/content
				]
			][
				map: copy scope
			]
			map/type: type
			;; these must be saved for each pen (in case we'll need to decode defaults):
			foreach attr [viewport #font-size] [map/:attr: get-value stack attr]
			map
		]
		
		emit-gradient: function [pen [word!] data [block!]] [
			grad: data/1
			switch length? stops: grad/content [
				0 [return compose [(pen) off]]
				2 [return compose [(pen) (stops/2)]]			;-- single stop should work as uniform fill
			]
			units: maybe-get-from-map grad #gradientUnits
			if scaled?: units = 'object [grad/viewport: (1,1)]	;-- '%' is relative to (1,1) by default
			foreach [word attr] [
				x1: #x1 y1: #y1 x2: #x2 y2: #y2 cx: #cx cy: #cy fx: #fx fy: #fy
				r: #r spread: #spreadMethod transform: #gradientTransform
			][
				set word maybe-get-from-map grad attr
			]
			require grad/element pick [ [x1 y1 x2 y2] [cx cy r] ] grad/type = 'linear
			require grad/element [units spread transform]
			altered?: either grad/type = 'linear [
				geom: compose [(as-point2D x1 y1) (as-point2D x2 y2)]
				geom <> [(0, 0) (1, 0)]
			][
				fx: any [fx cx]  fy: any [fy cy]				;-- these two default to 'cx,cy' ;@@ use 'default'
				geom: compose [(as-point2D cx cy) (r) (as-point2D fx fy)]
				geom <> [(0.5, 0.5) 0.5 (0.5, 0.5)]
			]
			if scaled? [
				if altered? [
					warn [
						"Draw does not support custom gradient geometry '"
						geom"' for objectBoundingBox mode"
					]
				]
				geom: []								;@@ the only way to scale it to the shape atm
			]
			transform: specialize-transform transform pen
			compose [(pen) (grad/type) (stops) (geom) (spread) (transform)]
		]
		
		emit-pattern: function [pen [word!] data [block!]] [
			warn ["None of the SVG pattern coordinate systems are supported by Draw; result may look different"]
			pat: data/1
			foreach [word attr] [
				units: #patternUnits cunits: #patternContentUnits
				x: #x y: #y w: #width h: #height transform: #patternTransform
			][
				set word maybe-get-from-map pat attr
			]
			if any [units = 'object cunits = 'object] [
				warn ["objectBoundingBox mode is not supported by Draw for pattern size"]
				return reduce [pen 'off]
			]
			start: as-point2D x y
			size:  as-point2D w h
			if start <> (0,0) [warn ["Draw doesn't support offsetting pattern tile"]]
			content: either pat/content [
				compose [(reset-draw) (init-draw) (next data) (pat/content)]	;-- apply viewbox transform to content
			][
				copy []
			]
			specialize-transform transform pen
			compose/deep [(pen) pattern (size) (0,0) (size) tile [(content)] (transform)]
		]
		
		emit-pen: function [pen [word!] color [tuple! word! string! none!] stack [block!] dict [map!] /blend opacity [number!]] [
			;@@ workaround for Draw treating 'pen' as 'fill-pen' for text and ignoring 'fill-pen'
			;@@ however it doesn't work if pen is defined above the textual element :/
			all [
				pen = 'fill-pen
				scope: stack/-1
				textual/(scope/element)
				pen: 'pen
			]
			result: only case [
				;; <animate>'s 'fill' attribute conflicts with 'fill' property, so this is to ignore it:
				find ["freeze" "remove"] color [copy []]
				string? color [
					ref: fetch-url color dict
					unless all [ref map? :ref/1] [fail-at color]
					either ref/1/type = 'pattern
						[emit-pattern  pen ref]					;-- pattern uses viewbox transforms from 'ref' 
						[emit-gradient pen ref]
				]
				color [
					#assert [any [tuple? color color = 'off]]
					reduce [pen color]
				]
			]
			opacity: any [opacity 1]							;@@ use 'default'
			apply-opacity/deep result opacity * get-total-opacity stack	;-- copies if modifies
		]
		
		#assert [
			[pen off]			= emit-pen 'pen 'off [] #[]
			[pen 1.2.3]			= emit-pen 'pen 1.2.3 [] #[]
			[]					= emit-pen 'pen none [] #[]		;-- unsupported color
			
			[fill-pen off] = emit-pen 'fill-pen "#grad" []		;-- no stops = no paint
				#["grad" [#[ element: linearGradient type: linear content: [] ]]]
				
			[fill-pen 1.1.1] = emit-pen 'fill-pen "#grad" []	;-- single stop = monochrome paint
				#["grad" [#[ element: linearGradient type: linear content: [0.0 1.1.1] ]]]
				
			[fill-pen linear 0.0 10.10.10 1.0 20.20.20 pad]
			= emit-pen 'fill-pen "#grad" []
				#["grad" [#[
					element: linearGradient type: linear content: [0.0 10.10.10 1.0 20.20.20]
				]]]
				
			[pen radial 0.0 10.10.10.128 1.0 20.20.20.128 (10,20) 130.0 (10,20) pad]
			= emit-pen 'pen "#grad" tail [#[#opacity 0.5]]
				#["grad" [#[
					element: radialGradient type: radial content: [0.0 10.10.10 1.0 20.20.20]
					#cx 10 #cy 20 #r 130 #gradientUnits user
				]]]
				
			equal?
				compose/deep [
					pen pattern (10, 20) (0, 0) (10, 20) tile [
						(reset-draw) (init-draw) fill-pen 0.1.2 box (1, 1) (2, 2)
					]
				]
				quiet [
					emit-pen 'pen "#pat" []
					#["pat" [#[
						element: pattern type: pattern content: [fill-pen 0.1.2 box (1,1) (2,2)]
						#width 10 #height 20 #patternUnits user
					]]]
				]
				
			; [pen off] = emit-pen 'pen "#invalid" [] #()		;@@ is this valid??
		]
		
		emit-viewport: function [						;-- establishes a new viewport; order: translate, clip, scale
			tgt-offset	[point2D!]
			tgt-size	[point2D!]
			viewbox		[block! none!]
			aspect		[block!]
			/topmost
		][
			buffer: make [] 12
			unless topmost [
				;; for topmost <svg> x and y must be ignored: https://www.w3.org/TR/SVG11/struct.html#SVGElement
				if tgt-offset <> (0,0) [into buffer [translate (tgt-offset)]]
				;; overflow='visible' for topmost and 'hidden' for others by default
				;@@ need to support it for more control: https://www.w3.org/TR/SVG11/masking.html#OverflowProperty
				into buffer [clip 0x0 (tgt-size)]
			]
			if viewbox [
				set [shift: fit?:] aspect
				set [src-offset: src-size:] viewbox
				fit-size: tgt-size
				if shift [
					scale:    tgt-size / src-size
					choose:   either fit? [:min][:max]
					fit-size: src-size * choose scale/x scale/y
				]
				free:   tgt-size - fit-size
				scale:  fit-size / src-size
				offset: free * any [shift 0]
				if (0,0) <> offset     [into buffer [translate (offset)]]
				if (1,1) <> scale      [into buffer [scale (scale/x) (scale/y)]]
				if (0,0) <> src-offset [into buffer [translate (negate src-offset)]]	;-- experimentally found out that it should be here :/
			]
			buffer
		]
		
		#assert [
			;@@ test viewport
		]
		
		;@@ fonts are scarce (see #4373), so may be abused, so font-cache may at least lessen the effects
		font-cache: make map! 4
		
		;@@ need a faster, by-design way to convert SVG font size into Red font size (REP #136)
		;@@ right now using a face to make measurements (slow, imprecise)
		rich-text-face: rtd-layout ["X"]
		rich-text-face/size: none
		
		make-font: function [stack [block!]] [
			foreach [word attr] [
				size:   #font-size   name:  #font-family
				weight: #font-weight style: #font-style
			][
				set word maybe-get-value stack attr
			]
			style: case [
				all [weight = 'bold style = 'italic] [copy [bold italic]]
				weight = 'bold   ['bold]
				style  = 'italic ['italic]
			]
			key: mold reduce [name size style]
			unless font: font-cache/:key [
				font-cache/:key: font: make font! compose [name: (name) size: 72]
				rich-text-face/font: font
				line-height: second size-text rich-text-face 
				rich-text-face/font: none
				font/size: round/to (size * 72 / line-height) 1	;@@ disable rounding once Red supports float size
				font/style: style
			]
			font
		]
		
		rich-text!: rtd-layout [""]						;-- used for measurements
		rich-text!/size: none
		
		measure-text: function [stack [block!] text [string!]] [
			rich-text!/font: get-value stack 'font
			; ?? rich-text!/font probe copy/part head stack stack 
			rich-text!/text: text
			size: size-text rich-text!
			rich-text!/text: rich-text!/font: none
			size
		]
		
		emit-text: function [stack [block!] text [string!]] [
			;; text offset is shared between text and all children, since children affect the parent
			text-pos: stack
			while [not head? text-pos] [				;@@ use 'locate'
				if text-pos/-1/element = 'text [break]
				text-pos: back text-pos
			]
			text-scope: text-pos/-1
			scope: stack/-1
			unless text-scope/offset [					;-- first emitted string
				foreach [word attr] [x: #x y: #y] [
					value: get-value/for text-pos attr 'text
					if other: maybe-get-value/for stack attr scope/element [	;-- allows tspans to override offset
						value: other
					]
					set word any [value/1 0]			;@@ offset is only supported for the whole string atm
				]
				text-scope/offset: as-point2D x y
			]
			size:   measure-text stack text
			anchor: get-value stack #text-anchor
			dir:    get-value stack #direction
			deco:	get-value stack #text-decoration
			if dir = 'left [anchor: 1 - anchor]
			;@@ 80% is a blind guess at baseline location in the line height - needs REP #136
			vshift: size/y * 80%
			hshift: anchor * size/x
			offset: text-scope/offset - as-point2D hshift vshift
			if deco <> 'none [
				either find [underline strike] deco [
					n: length? text
					text: rtd-layout reduce [text]
					text/size: none
					text/font: get-value stack 'font
					text/data: reduce [as-pair 1 n  deco]
				][
					warn ["Text decoration '"deco"' is not supported by Draw"]
				]
			]
			result: compose emit-rules/text!
			text-scope/offset/x: text-scope/offset/x + size/x
			result
		]
		
		;; inner elements (content) are added automatically, don't need a mention here
		;; '?' stands for "no error if no value", 'L' for as-point2D constructor (dialect is preprocessed below)
		;@@ width/height/r of zero should completely disable shape rendering
		emit-rules: make map! [
			;@@ rect of zero height/width, and ellipse of zero rx/ry must not be rendered
			rect		[box  (xy: L#x #y)  (xy + L#width #height)	;@@ box only supports symmetric rounding radius
						 (
						 	len: len? any [?#rx ?#ry 0] any [?#ry ?#rx 0]	;-- https://www.w3.org/TR/SVG11/shapes.html#RectElementRYAttribute
						 	only if len > 0 [len]		;@@ workaround for #5383
						 )]
			circle		[circle  (L#cx #cy) (#r)]
			ellipse		[ellipse (subtract L#cx #cy L#rx #ry) (2 * L#rx #ry)]
			line		[line    (L#x1 #y1) (L#x2 #y2)]
			polyline	[line    (#points)]
			polygon		[polygon (#points)]
			path		[shape   [(#d)]]
			defs		[]
			g			[]
			svg			[]
			stop		[(alpha-blend #stop-color #stop-opacity) (1.0 * #offset)]
			animate		[]								;@@ not supported
			text!		[text (offset) (text)]			;-- see 'emit-text'
			font!		[font (value)]					;-- emits special 'font' attribute, not 'font' SVG element
			text		[]								;-- these need no special handling
			tspan		[]								
			
			;; at place of definition gradient is emitted as [#(scope) stops...] block, and saved by #id in this form
			;; at place of insertion it will be formed into a 'pen' command
			linearGradient [(flatten-pen stack dict 'linear)]
			radialGradient [(flatten-pen stack dict 'radial)]
			
			;; at place of definition pattern is emitted as [#(scope) transforms...] block, and saved by #id in this form
			;; at place of insertion it will be formed into a 'pen' command
			pattern        [(flatten-pen stack dict 'pattern)]
			
			#id					[(ignore dict/:value: result)]
			#stroke-width		[line-width (value)]
			#stroke-linecap		[line-cap (value)]
			#stroke-linejoin	[line-join (value)]
			#viewBox			[]						;-- ignored: see special case in 'emit-element'
			#preserveAspectRatio[]						;-- ignored: ditto
			#transform			[]						;-- ignored: see special case in 'emit-element'
			#stroke				[(emit-pen/blend 'pen      value stack dict any [?#stroke-opacity 1])]
			#fill				[(emit-pen/blend 'fill-pen value stack dict any [?#fill-opacity   1])]
			;; font is saved in scope so it can be accessed later by <text> and <tspan> emitters
			;; they need it to measure text size, in order to compute offset at the end of the text
			
			#font-size			[]						;-- font props are not emitted as is, but gathered into a /font attribute
			#font-family		[]						;-- /font is required to measure text size, in order to compute offset at its end
			
			;; SVG attributes are used by elements, not emitted directly
			#x [] #y [] #x1 [] #y1 [] #x2 [] #y2 [] #cx [] #cy [] #rx [] #ry [] #r [] #d [] #points [] #width [] #height []
			#color [] #offset [] #stop-color [] #stop-opacity []
			#patternTransform [] #gradientTransform [] #patternUnits [] #gradientUnits []
			
			;; just bloat; ignored
			desc [] title [] parent [] space [] base [] #xmlns [] #version [] #svg [] #xlink []
		];emit-rules: make map! [
		
		;; called on an element when all of its children are emitted into scope/content, and all attrs/props in the tree decoded
		emit-element: function [stack [block!] dict [map!] /local xy len] [
			scope:  stack/-1
			elem:   scope/element
			result: make [] 8
			
			;; special case: transform precedes all other attributes: https://www.w3.org/TR/SVG11/coords.html#TransformAttribute
			append result only if transforming/:elem [scope/#transform]		;-- 'transform' is ready for emit once decoded
			
			;; emit all other attributes except transform
			foreach [attr value] scope [				;@@ use for-each to filter attr
				unless issue? attr [continue]
				any [
					if rule: emit-rules/:attr [compose/into rule tail result]
					warn ["Unsupported attribute '"attr"' is ignored"]
				]
			]
			if value: scope/font [compose/into emit-rules/font! tail result]
			
			;; emit the element
			any [
				if rule: emit-rules/:elem [compose/deep/into rule tail result]
				warn ["Unsupported element '"elem"' is ignored"]
			]
			
			;; special case: viewBox must follow (all?) other attributes: https://www.w3.org/TR/SVG11/coords.html#ViewBoxAttribute
			;; 'viewBox' also requires other attributes for it to have any meaning
			if deforming/:elem [
				foreach [word attr] [x: #x y: #y w: #width h: #height aspect: #preserveAspectRatio] [
					set word get-value/for stack attr elem
				]
				topmost: (index? stack) <= 2
				append result emit-viewport/:topmost as-point2D x y as-point2D w h scope/#viewBox aspect
			]
			
			;; emit children (already processed and emitted into scope/content)
			append result only scope/content
			
			;; ignored result may still be present as #id in dict, but not emitted as Draw code
			only if not ignored/:elem [result]
		]
		
		hide with [attr: opt?: none] [					;-- expand rules dialect into Red code
			foreach [key template] emit-rules [
				parse template rule: [any [
					change only [set opt? opt '? set attr issue!] (
						getter: either opt? ['maybe-get-value/for]['get-value/for]
						as paren! compose [(getter) ([(stack)]) (attr) ([(elem)])]
					)
				|	into rule
				|	skip
				]]
				bind template :emit-element
			]
			bind emit-rules/text! :emit-text
		]
		
		
		
		;; * * * * * * * * * * * * *
		;; *** PRIMARY INTERFACE ***
		;; * * * * * * * * * * * * *
		
		
		enter: function [stack [block!]] [
			either tail? stack [append stack make map! 16][clear stack/1]
			next stack
		]
		leave: function [stack [block!]] [back stack]
		
		;; 'decode' also deals with explicit "inherit"ance, so other functions don't need to
		;; 'stack' cannot be replaced by function's internal stack, since we need access to all elements up to root
		decode: function [
			"Turn XML element(s) into a Draw block"
			data  [block!] "Decoded XML markup in 'compact' mode"
			stack [block!] "Entered elements stack as block of maps"
			dict  [map!]   "Registered #ids (unique per-file)"
			/on canvas [pair! point2D!] "Initial viewport size (defaults to 100x100)"
			/local elem-name attr-ns attr-name attr-data text
		][
			result: make [] 2							;-- [push [element1] push [element2] ...]
			upper:  any [stack/-1 #[]]
			parse data [any [							;-- accepts any number of elements
				opt refinement!
				set elem-name word!
				ahead block! into [;source:
					(
						stack: enter stack
						scope: stack/-1
						if canvas [scope/viewport: to point2D! canvas]
					)
					any [								;-- collect attributes before emitting element
						;; unlike 'transform', 'svg:transform' must be ignored:
						;; https://www.w3.org/TR/SVG11/coords.html#SVGGlobalTransformAttribute
						; /svg #transform skip
					; |
						set attr-ns opt /xlink			;-- xlink is the only namespace used, the rest is ignored
						set attr-name issue!
						set attr-data string!
						(
							either attr-data = "inherit" [
								;; explicit inheritance in SVG only works with the immediate parent
								;; if nothing to inherit, attribute is not assigned
								if upper/:attr-name [scope/:attr-name: upper/:attr-name]
							][
								scope/:attr-name: attr-data
							]
						)
					|
						refinement! 2 skip				;-- we don't know how to decode other namespaces, so skip them
					]
					inner: to end
					(
						scope/element: elem-name
						; scope/source:  source			;-- used by text
						decode-attributes stack
						scope/content: decode inner stack dict
						elem: emit-element stack dict
						stack: leave stack
						unless tail? elem [
							either flat/:elem-name [
								append result elem
							][
								repend result ['push elem]
							]
						]
					)
				]
			|	'text! set text string!
				(
					all [
						scope: stack/-1
						textual/(scope/element)
						append result emit-text stack text		;-- uses and modifies scope/offset
					]
				)
			| end | p: (fail-at p)
			]];parse data [any [
			result
		];decode: function [
		
	];internal: context [
	
	#assert [
		[] = decode []
		;@@ TODO
	]
	
];put system/codecs 'svg context [

 