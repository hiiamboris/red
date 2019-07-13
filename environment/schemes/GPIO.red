Red [
	Title:   "GPIO port scheme"
	Author:  "Nenad Rakocevic"
	File: 	 %GPIO.red
	Tabs:	 4
	Rights:  "Copyright (C) 2011-2019 Red Foundation. All rights reserved."
	License: {
		Distributed under the Boost Software License, Version 1.0.
		See https://github.com/red/red/blob/master/BSL-License.txt
	}
	Notes: {
		For Raspberry Pi boards only for now.
		Low-level GPIO code largely inspired by http://wiringpi.com/
	}
]

gpio-scheme: context [

	#system [
		gpio: context [
			#import [
				LIBC-file cdecl [
					mmap: "mmap" [
						address		[byte-ptr!]
						size		[integer!]
						protection	[integer!]
						flags		[integer!]
						fd			[integer!]
						offset		[integer!]
						return:		[byte-ptr!]
					]
					munmap: "munmap" [
						address		[byte-ptr!]
						size		[integer!]
						return:		[integer!]
					]
				]
			]

			#define RPI_GPIO_PERIPH_RPI23	3F000000h	;-- RPi 2 & 3 peripherals
			#define RPI_GPIO_PERIPH_RPI01	20000000h	;-- RPi zero & 1 peripherals
			#define RPI_GPIO_OFFSET			00200000h
			#define RPI_GPIO_PWM			0020C000h
			#define RPI_GPIO_CLOCK_BASE		00101000h
			
			#define RPI_BCM_PASSWORD		5A000000h
			
			#define RPI_PWMCLK_CNTL			40
 			#define RPI_PWMCLK_DIV			41

			#enum gpio-pins! [
				GPFSEL0:   	00h
				GPFSEL1:   	04h
				GPFSEL2:   	08h
				GPFSEL3:   	0Ch
				GPFSEL4:   	10h
				GPFSEL5:   	14h
				GPSET0:    	1Ch
				GPSET1:    	20h
				GPCLR0:    	28h
				GPCLR1:    	2Ch
				GPLEV0:    	34h
				GPLEV1:    	38h
				GPEDS0:    	40h
				GPEDS1:    	44h
				GPREN0:    	4Ch
				GPREN1:    	50h
				GPFEN0:    	58h
				GPFEN1:    	5Ch
				GPHEN0:    	64h
				GPHEN1:    	68h
				GPLEN0:    	70h
				GPLEN1:    	74h
				GPAREN0:   	7Ch
				GPAREN1:   	80h
				GPAFEN0:   	88h
				GPAFEN1:   	8Ch
				GPPUD:     	94h
				GPPUDCLK0: 	98h
				GPPUDCLK1: 	9Ch
			]

			#enum pin-modes! [
				MODE_INPUT: 0
				MODE_OUTPUT
				MODE_PWM_OUTPUT
				MODE_GPIO_CLOCK
				MODE_4									;-- not defined yet
				MODE_5
				MODE_6
			]

			#enum pull-updown! [
				PUD_OFF: 0
				PUD_DOWN
				PUD_UP
			]

			#enum pin-values! [
				LOW: 0
				HIGH
			]
			
			#enum pwm-control! [
				PWM_CONTROL:	0
				PWM_STATUS:		1
				PWM0_RANGE:		4
				PWM0_DATA:		5
				PWM1_RANGE:		8
				PWM1_DATA:		9
			]
			
			#enum pwm-modes! [
				PWM0_MS_MODE:	0080h					;-- Run in MS mode
				PWM0_USEFIFO:	0020h					;-- Data from FIFO
				PWM0_REVPOLAR:	0010h					;-- Reverse polarity
				PWM0_OFFSTATE:	0008h					;-- Ouput Off state
				PWM0_REPEATFF:	0004h					;-- Repeat last value if FIFO empty
				PWM0_SERIAL:	0002h					;-- Run in serial mode
				PWM0_ENABLE:	0001h					;-- Channel Enable
				PWM1_MS_MODE:	8000h					;-- Run in MS mode
				PWM1_USEFIFO:	2000h					;-- Data from FIFO
				PWM1_REVPOLAR:	1000h					;-- Reverse polarity
				PWM1_OFFSTATE:	0800h					;-- Ouput Off state
				PWM1_REPEATFF:	0400h					;-- Repeat last value if FIFO empty
				PWM1_SERIAL:	0200h					;-- Run in serial mode
				PWM1_ENABLE:	0100h					;-- Channel Enable
			]
			
			regions: [RPI_GPIO_OFFSET RPI_GPIO_PWM RPI_GPIO_CLOCK_BASE]

			set-mode: func [
				base [byte-ptr!]
				pwm	 [byte-ptr!]
				clk	 [byte-ptr!]
				pin	 [integer!]
				mode [integer!]
				/local
					GPFSEL [int-ptr!]
					index  [integer!]
					shift  [integer!]
					mask   [integer!]
					bits   [integer!]
					alt	   [integer!]
			][
				index: pin * CDh >> 11
				shift: pin - (index * 10) * 3
				GPFSEL: as int-ptr! (base + (index << 2))
				mask: GPFSEL/value and not (7 << shift)
				bits: either mode <> MODE_PWM_OUTPUT [mode][
					alt: switch pin [
						12 13   [4]						;-- FSEL_ALT0
						18 19   [2]						;-- FSEL_ALT5
						default [probe "invalid pin" 0]
					]
				]
				GPFSEL/value: bits << shift or mask
				
				if mode = MODE_PWM_OUTPUT [
					platform/usleep 110
					pwm-set-mode pwm 1					;-- PWM_MODE_BAL
					pwm-set-range pwm 1024
					pwm-set-clock pwm clk 32			;-- 600KHz, starts the PWM
				]
			]

			set: func [
				base [byte-ptr!]
				pin	  [integer!]
				high? [logic!]
				/local
					p	  [int-ptr!]
					index [integer!]
					bit	  [integer!]
					mode  [integer!]
			][
				index: pin >> 3							;-- pin >> 5 * 4
				bit: 1 << (pin and 31)

				mode: either high? [GPSET0][GPCLR0]
				p: as int-ptr! (base + mode + index)
				p/value: bit
			]

			get: func [
				base    [byte-ptr!]
				pin	    [integer!]
				return: [integer!]
				/local
					p	  [int-ptr!]
					bit	  [integer!]
			][
				bit: 1 << (pin and 31)
				p: as int-ptr! (base + GPLEV0)
				either p/value and bit <> 0 [1][0]
			]

			set-pull: func [
				base	[byte-ptr!]
				pin		[integer!]
				pud		[integer!]
				/local
					p	[int-ptr!]
			][
				p: as int-ptr! (base + GPPUD)
				p/value: pud and 3
				platform/usleep 5

				p: as int-ptr! (base + GPPUDCLK0)
				p/value: 1 << (pin and 31)
				platform/usleep 5

				p: as int-ptr! (base + GPPUD)
				p/value: 0
				platform/usleep 5

				p: as int-ptr! (base + GPPUDCLK0)
				p/value: 0
				platform/usleep 5
			]
			
			;-- Select the native "balanced" mode, or standard mark:space mode
			pwm-set-mode: func [
				pwm	 [byte-ptr!]
				mode [integer!]							;-- 0: PWM_MODE_MS, 1: PWM_MODE_BAL
				/local
					p	 [int-ptr!]
					bits [integer!]
			][
				bits: PWM0_ENABLE or PWM1_ENABLE
				if zero? mode [bits: bits or PWM0_MS_MODE or PWM1_MS_MODE]
				p: as int-ptr! (pwm + PWM_CONTROL)
				p/value: bits
			]
			
			pwm-set-range: func [
				pwm	  [byte-ptr!]
				range [integer!]
				/local
					p [int-ptr!]
			][
				p: as int-ptr! (pwm + PWM0_RANGE)
				p/value: range
				platform/usleep 10
				
				p: as int-ptr! (pwm + PWM1_RANGE)
				p/value: range
				platform/usleep 10
			]
			
			pwm-set-clock: func [
				pwm		[byte-ptr!]
				clk		[byte-ptr!]
				divisor [integer!]
				/local
					p	  [int-ptr!]
					c	  [int-ptr!]
					cd	  [int-ptr!]
					saved [integer!]
			][
				divisor: divisor and 4095
				p: as int-ptr! (pwm + PWM_CONTROL)
				saved: p/value
				p/value: 0								;-- stop PWM
				
				c: as int-ptr! (clk + RPI_PWMCLK_CNTL)
				c/value: RPI_BCM_PASSWORD or 1			;-- stop PWM clock
				platform/usleep 110
				
				while [c/value and 80h <> 0][platform/usleep 1]
				
				cd: as int-ptr! (clk + RPI_PWMCLK_DIV)
				cd/value: RPI_BCM_PASSWORD or (divisor << 12)
				c/value: RPI_BCM_PASSWORD or 11h		;-- start PWM clock
				p/value: saved
			]
		]
	]
	
	models: [
	;-- Name ---------- Mapping --
		"Model A"		old
		"Model B"		old
		"Model A+"		old
		"Model B+"		old
		"Pi 2"			new
		"Alpha"			old
		"CM"			old
		"Unknown07"		new
		"Pi 3"			new
		"Pi Zero"		old
		"CM3"			new
		"Unknown11"		new
		"Pi Zero-W"		old
		"Pi 3B+"		new
		"Pi 3A+"		new
		"Unknown15"		new
		"CM3+"			new
		"Unknown17"		new
		"Unknown18"		new
		"Unknown19"		new
	]
	
	gpio.open: routine [
		state [block!]
		old?  [logic!]
		/local
			handle [red-handle!]
			fd	   [integer!]
			model  [integer!]
			base   [byte-ptr!]
			i	   [integer!]
	][
		fd: platform/io-open "/dev/gpiomem" 00101002h	;-- O_RDWR or O_SYNC
		if fd > 0 [
			handle: as red-handle! block/rs-head state
			handle/header: TYPE_HANDLE
			handle/value: fd
			model: either old? [RPI_GPIO_PERIPH_RPI01][RPI_GPIO_PERIPH_RPI23]

			i: 1
			until [
				base: gpio/mmap null 4096 MMAP_PROT_RW MMAP_MAP_SHARED fd model or gpio/regions/i
				if -1 <> as-integer base [
					handle: handle + 1
					handle/header: TYPE_HANDLE
					handle/value: as-integer base
				]
				i: i + 1
				i > gpio/regions/0
			]
		]
	]
	
	gpio.set-mode: routine [base [handle!] pwm [handle!] clk [handle!] pin [integer!] mode [integer!]][
		gpio/set-mode as byte-ptr! pwm/value as byte-ptr! base/value as byte-ptr! clk/value pin mode - 1
	]
	
	gpio.set: routine [base [handle!] pin [integer!] value [integer!]][
		gpio/set as byte-ptr! base/value pin as-logic value
	]
	
	gpio.set-pull: routine [base [handle!] pin [integer!] value [integer!]][
		gpio/set-pull as byte-ptr! base/value pin value - 1
	]
	
	gpio.get: routine [base [handle!] pin [integer!] return: [integer!]][
		gpio/get as byte-ptr! base/value pin
	]

	gpio.close: routine [
		state [block!]
		/local
			handle [red-handle!]
	][
		handle: as red-handle! (block/rs-head state) + 3
		loop 3 [
			if zero? gpio/munmap as byte-ptr! handle/value 4096 [handle/header: TYPE_NONE]
			handle: handle - 1
		]
		if zero? platform/io-close handle/value [handle/header: TYPE_NONE]
	]
	
	gpio.pause: routine [us [integer!]][platform/usleep us * 1000]

	;--- Port actions ---

	open: func [port /local state info revision model err i][
		unless attempt [info: read %/proc/cpuinfo][
			cause-error 'access 'cannot-open ["cannot access /proc/cpuinfo"]
		]
		parse/case info [thru "Revision" thru #":" any #" " copy revision to lf]
		revision: to-integer debase/base revision 16
		model: FFh << 4 and revision >> 4
		
		;-- fd (handle!), base (handle!), pwm (handle!), clk (handle!)
		state: port/state: copy [none none none none]
		gpio.open port/state 'old = pick models model + 1 * 2 	;-- model is 0-based
		
		err: ["failed to open /dev/gpiomem" "base mmap() failed" "pwm mmap() failed"]
		repeat i 3 [unless state/:i [cause-error 'access 'cannot-open [err/:i]]]
	]
	
	insert: func [port data [block!] /local base modes value pulls pos m list v][
		unless all [block? s: port/state parse s [4 handle!]][
			cause-error 'access 'not-open ["port/state is invalid"]
		]
		modes: [['in | 'input] (m: 1) | ['out | 'output] (m: 2) | 'pwm (m: 3)]	;-- order matters
		value: [m: logic! | ['on | 'high] (m: yes) | ['off | 'low] (m: no) | m: integer!]
		pulls: ['pull-off (m: 1) | 'pull-down (m: 2) | 'pull-up (m: 3)] ;-- order matters
		list: none
		base: s/2
		
		unless parse data [
			some [pos:
				  'set-mode    integer! modes (gpio.set-mode base s/3 s/4 pos/2 m)
				| 'set         integer! value (gpio.set base pos/2 make integer! m)
				| pulls        integer!       (gpio.set-pull base pos/2 m)
				| 'get         integer!       (d: gpio.get base pos/2
					switch/default type?/word list [
						block! [append list d]
						none!  [list: d]
					][append list: reduce [list] d]
				)
				| 'pause [integer! | float!] (
					gpio.pause either float? v: pos/2 [to-integer v * 1000][v]
				)
			]
		][cause-error 'access 'invalid-cmd [data]]
		
		port/data: list
	]

	close: func [port /local state err i][
		gpio.close state: port/state
		err: ["failed to close /dev/gpiomem" "base mmunap() failed" "pwm mmunap() failed"]
		repeat i 4 [if handle? state/:i [cause-error 'access 'cannot-close [err/:i]]]
	]
]

register-scheme make system/standard/scheme [
	name: 'GPIO
	title: "GPIO access for Raspberry Pi boards"
	actor: gpio-scheme
]


#example [
	p: open gpio://

	insert p [set-mode 4 out]
	loop 20 [
		insert p [set 4 on]
		wait 0.1
		insert p [set 4 off]
		wait 0.1
	]

	insert p [
		set-mode 17 in
		pull-down 17
	]
	loop 10 [
		insert p [get 17]
		probe p/data
		wait 0.5
	]

	close p
 ]