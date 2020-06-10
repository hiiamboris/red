Red [
	Title:	"Reactive programming support"
	Author: "Nenad Rakocevic"
	File: 	%reactivity.red
	Tabs: 	4
	Rights: "Copyright (C) 2016-2020 Red Foundation. All rights reserved."
	License: {
		Distributed under the Boost Software License, Version 1.0.
		See https://github.com/red/red/blob/master/BSL-License.txt
	}
]

reactor!: context [
	on-change*: function [word old new][
		if system/reactivity/debug? [
			print [
				"-- on-change event --" lf
				tab "word :" word		lf
				tab "old  :" type? :old	lf
				tab "new  :" type? :new
			]
		]
		all [
			not empty? srs: system/reactivity/source
			srs/1 =? self
			srs/2 = word
			set-quiet in self word old					;-- force the old value
			exit
		]
		unless all [block? :old block? :new same? head :old head :new][
			if any [series? :old object? :old][modify old 'owned none]
			if any [series? :new object? :new][modify new 'owned reduce [self word]]
		]
		system/reactivity/check/only self word
	]
]

deep-reactor!: make reactor! [
	on-deep-change*: function [owner word target action new index part][
		system/reactivity/check/only owner word
	]
]

reactor:	  function [spec [block!]][make reactor! spec]
deep-reactor: function [spec [block!]][make deep-reactor! spec]


system/reactivity: context [
	;-- relations format: [reactor word reaction targets]
	;;  reactor src-word [reaction] set-word             -- used by `is` (evaluates reaction, assigns to target)
	;;  reactor src-word function [func obj1 obj2...]    -- used by react/link (evaluates target), one relation for every reactor in both list and func's body
	;;  reactor src-word [reaction] none                 -- used by react (evaluates reaction)
	;;  reactor src-word [reaction] set-word/object      -- used by react/with (evaluates reaction, assigns to a set-word only)
	relations:	 make block! 1000						;@@ change it to hash! once stable

	;-- queue format: [reactor reaction target done]
	queue:		 make block! 100

	debug?: 	 no	
	source:		 []		;-- contains the initial [reactor reaction] that triggered a chain of subsequent reactions

	add-relation: func [
		obj		 [object!]
		word
		reaction [block! function!]
		targets  [set-word! block! object! none!]
		/local new-rel pos
	][
		new-rel: reduce [obj :word :reaction targets]
		unless find/same/skip relations new-rel 4 [append relations new-rel]
	]
	
	eval: function [code [block!] /safe /local result][
		either safe [
			if error? error: try/all [set/any 'result do code  'ok] [
				print :error
				prin "*** Near: "
				print mold/part/flat code 80
			]
			:result
		][
			do code
		]
	]
	
	eval-reaction: func [reactor [object!] reaction [block! function!] target [set-word! block! object! none!]][
		either set-word? target [
			set/any target eval/safe :reaction
		][
			eval/safe any [all [block? :reaction reaction] target]
		]
	]
	
	pending?: function [reactor [object!] reaction [block! function!]][
		q: queue
		while [q: find/same/skip q reactor 4][
			if :q/2 =? :reaction [return yes]
			q: skip q 4
		]
		no
	]

	check: function [reactor [object!] /only field [word! set-word!] /local _ word reaction target][
		if empty? pos: relations [exit]
		while [pos: find/same/skip pos reactor 4][
			set [_ word reaction target] pos
			pos: skip pos 4
			if all [only  word <> field] [continue]
			if pending? reactor :reaction [continue]
			unless tail? queue [						;-- entered while another reaction is running
				repend queue [reactor :reaction target no]
				continue
			]
			if empty? source [
				append append source reactor field
			]
			repend queue [reactor :reaction target yes]
			eval-reaction reactor :reaction target
			
			q: tail queue
			until [
				q: skip q': q -4
				either q/4 [ 							;-- was already executed?
					clear q 							;-- allow requeueing of it
				][
					eval-reaction q/1 :q/2 q/3
					either tail? q' [ 					;-- queue wasn't extended
						clear q 						;-- allow requeueing
					][
						q/4: yes 						;-- mark as executed
						q: tail q	 					;-- jump to recently queued reactions
					]
				]
				head? q
			]
			clear queue
			clear source
		]
	]
	
	set 'stop-reactor function [
		"Forget all relations involving reactor OBJ"
		obj [object!] "Face or reactor"
		/deep "Deeply remove all relations from child faces"
	][
		list: relations
		while [not tail? list][
			either any [
				same? list/1 obj
				all [
					block? list/4						;-- react/link with this face as argument case
					find/same list/4 obj
				]
			][
				remove/part list 4
			][
				list: skip list 4
			]
		]
		if all [deep block? :obj/pane] [
			foreach f obj/pane [stop-reactor/deep f]
		]
	]
	
	set 'clear-reactions function ["Remove all reactive relations"][
		clear relations
	]
	
	set 'dump-reactions function [
		"Output all the current reactive relations for debugging purpose"
	][
		limit: (any [all [system/console system/console/size/x] 72]) - 10
		count: 0
		
		foreach [obj field reaction target] relations [
			prin count: count + 1
			prin ":---^/"
			prin "  Source: object "
			list: words-of obj
			remove find list 'on-change*
			remove find list 'on-deep-change*
			print mold/part list limit - 5
			prin "   Field: "
			print form field
			prin "  Action: "
			print mold/flat/part :reaction limit
			case [
				block? target [
					prin "    Args: "
					print copy/part replace/all mold/flat/part next target limit + 20 "make object!" "object" limit
				]
				set-word? target [
					prin "  Target: "
					print form target
				]
			]
		]
		()												;-- avoids returning anything in the console
	]
	
	is~: function [
		"Defines a reactive relation whose result is assigned to a word"
		'field	 [set-word!]	"Set-word which will get set to the result of the reaction"
		reaction [block!]		"Reactive relation"
	][
		obj: context? field
		parse reaction rule: [
			any [
				item: [word! | get-word! | lit-word!]
					(if in obj item/1 [add-relation obj to word! item/1 reaction field])
				| any-path! | any-string!
				| into rule
				| skip
			]
		]
		react/later/with reaction field
		set field either block? :reaction/1 [do :reaction/1][eval reaction]
	]
	
	set 'is make op! :is~
	
	set 'react? function [
		"Returns a reactive relation if an object's field is a reactive source"
		reactor	[object!]	"Object to check"
		field	[word!]		"Field to check"
		/target				"Check if it's a target instead of a source"
		return: [block! function! word! none!] "Returns reaction, type or NONE"
	][
		either target [
			pos: skip relations 3
			while [pos: find/skip pos field 4][
				if reactor =? context? pos/1 [return pos/-1]
				pos: skip pos 4
			]
		][
			pos: relations
			while [pos: find/same/skip pos reactor 4][
				if pos/2 = field [return pos/3]
				pos: skip pos 4
			]
		]
		none
	]
	
	set 'react function [
		"Defines a new reactive relation between two or more objects"
		reaction	[block! function!]	"Reactive relation"
		/link							"Link objects together using a reactive relation"
			objects	[block!]			"Objects to link together"
		/unlink							"Removes an existing reactive relation"
			src		[word! object! block!] "'all word, or a reactor or a list of reactors"
		/later							"Run the reaction on next change instead of now"
		/with							"Specifies an optional face object (internal use)"
			ctx		[object! set-word! none!] "Optional context for VID faces or target set-word"
		return:		[block! function! none!] "The reactive relation or NONE if no relation was processed"
	][
		case [
			link [
				unless function? :reaction [cause-error 'script 'react-bad-func []]
				objs: parse spec-of :reaction [
					collect some [keep word! | [refinement! | set-word!] break | skip]
				]
				if empty? objs [cause-error 'script 'react-not-enough []]
				objects: reduce objects
				
				if (length? objects) <> length? objs [cause-error 'script 'react-no-match []]
				unless parse objects [some object!][cause-error 'script 'react-bad-obj []]
				
				insert objects :reaction
				
				found?: no
				parse body-of :reaction rule: [
					any [
						item: [path! | lit-path! | get-path!] (
							item: item/1
							if pos: find objs item/1 [
								obj: pick objects 1 + index? pos
								add-relation obj item/2 :reaction objects
								found?: yes
							]
						)
						| set-path! | any-string!
						| into rule
						| skip
					]
				]
				if all [found? not later] [eval objects]
			]
			unlink [
				found?: no
				cond: case [
					src =  'all [[true]]
					object? src [[src =? obj]]
					block?  src [src: reduce src  [find/same src obj]]
					'else       [cause-error 'script 'invalid-arg [src]]
				]
				pos: skip relations 2
				while [pos: find/same/only/skip pos :reaction 4][
					obj: pos/-2
					if any cond [
						remove/part skip pos -2 4
						found?: yes
					][
						pos: skip pos 4
					]
				]
			]
			'else [
				found?: no
				parse reaction rule: [
					any [
						item: [path! | lit-path! | get-path!] (
							saved: item/1
							if unset? attempt [get/any item: saved][
								cause-error 'script 'no-value [item]
							]
							either 2 = length? item [
								set/any 'obj get/any item/1
								part: 1
							][
								part: length? item
								until [					;-- search for an object (deep first)
									part: part - 1
									path: copy/part item part
									any [
										tail? path
										object? obj: attempt [get path]
										part = 1
									]
								]
							]
							if all [
								object? :obj			;-- rough checks for reactive object
								in obj 'on-change*
							][
								part: part + 1
								add-relation obj item/:part reaction ctx
								found?: yes
							]
							parse saved rule
						)
						| set-path! | any-string!
						| into rule
						| skip
					]
				]
				if all [found? not later] [eval reaction]
			]
		]
		either found? [:reaction][none]					;-- returns NONE if no relation was processed
	]
]

