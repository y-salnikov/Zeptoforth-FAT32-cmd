begin-module fat32-cmd

	begin-module fat32-cmd-internal
		
		oo import
		fat32-tools import
		fat32-tools-internal import
		fat32 import
		lock import
		rtc import
		

		: size-human-readable ( u -- )
			.							\ for now
		;
		: char-in-string? { str len u-char -- flag }
			false
			len 0 do
				str i + c@ u-char = if
					drop true
					leave
				then
			loop
		;

		: dir-entries-num { path_adr path_n -- N }
			path_adr path_n
			[:
				[: 
					<fat32-entry> class-size [:
						0 { dir entry entries-count }
						entry dir
						ram-here { fn-buf }
						12 ram-allot
						begin
							2dup read-dir if
									fn-buf 12 3 pick file-name@ { fn_a fn_l }
									fn_a fn_l s" ." equal-strings? not if
									fn_a fn_l s" .." equal-strings? not if
											1 +to entries-count
										then
									then
									false
							else
								2drop true
							then
						until
						fn-buf ram-here!
						entries-count
					;] with-aligned-allot
				;] current-fs@ with-open-dir-at-root-path
			;] fs-lock with-lock

		;

		: for-each-in-dir { tkn n xt -- }  ( xt: fn_adr fn_len -- )

			tkn n dir-entries-num { entries-count }	
			ram-here { fnpad }
			entries-count 12 * ram-allot
			ram-here { tmppad } 12 ram-allot

			tmppad
			fnpad
			tkn n
			[:
				[: 
					<fat32-entry> class-size [: { tmppad fnpad dir entry }
						0 { idx }
						entry dir
						begin
							2dup read-dir if
								tmppad 12 3 pick file-name@ { fn_a fn_l }
								fn_a fn_l s" ." equal-strings? not if
								fn_a fn_l s" .." equal-strings? not if
										fnpad idx 12 * + 12 bl fill
										fn_a fnpad idx 12 * + fn_l move
										1 +to idx
									then
								then
								false
							else
								2drop true
							then
						until
					;] with-aligned-allot
				;] current-fs@ with-open-dir-at-root-path
			;] fs-lock with-lock
			0 tmppad !
			fnpad { fnptr }
			begin
				fnptr 12 compat::-trailing xt execute
				12 +to fnptr
			fnptr c@ 0= until
			fnpad ram-here!
		;

		: filenames> { fn1_adr fn2_adr -- result }
			false { finish }
			0 { counter }
			false { result }

			begin
				counter fn1_adr + c@ dup [char] / = if drop 0 then counter fn2_adr  + c@ dup [char] / = if drop 0 then 2dup > if true to finish true to result then
																< if true to finish false to result then
				1 +to counter
				counter 12 = if true to finish then
			finish until
			result
		;

		: ls ( word -- )
			current-fs@ averts x-fs-not-set
			cr
			0 1 0 { long sorted dates }
			token { tkn n }
			tkn c@ [char] - = if
				
				tkn n [char] h char-in-string? if
							." ls [-lua] <path>" cr
							." -l:  long format, one column" cr
							." -u:  unsorted " cr
							." -a:  all info (with dates)" cr
							." Options can be combined like: -la" cr
				then
				tkn n [char] l char-in-string? if true to long then
				tkn n [char] u char-in-string? if false to sorted then
				tkn n [char] a char-in-string? if true to dates then

				token to n to tkn
			then

			
			tkn n
			[:
				[: 
					<fat32-entry> class-size [:
						0 0 { dir entry entries-count dir-count }
						entry dir
						begin
							2dup read-dir if
									1 +to entries-count
									over entry-dir? if 1 +to dir-count then
									false
							else
								2drop true
							then
						until
						entries-count dir-count
					;] with-aligned-allot
				;] current-fs@ with-open-dir-at-root-path
			;] fs-lock with-lock
			{ entries-count dir-count }


				ram-here { names-buf }
				entries-count 13 * ram-allot
				4 ram-align,
				ram-here { sort-buf }
				entries-count cells ram-allot
				ram-here { len-buf }
				entries-count cells  ram-allot
				ram-here { date-buf }
				entries-count date-time-size 2* * ram-allot 4 ram-align,
				
				entries-count 0> if
				
				names-buf sort-buf len-buf date-buf entries-count dir-count
				
				tkn n
				[:
					[:		
						<fat32-entry> class-size [:
							
							{ names-buf sort-buf len-buf date-buf entries-count dir-count dir entry }

							0 0 0 { dir-idx file-idx idx }
							entry dir
							begin
								2dup read-dir if
									over entry-dir? if
										dir-idx to idx
										1 +to dir-idx
										names-buf idx 13 * + dup 13 bl fill
										12 3 pick file-name@ + [char] / swap c!
									else
										dir-count file-idx + to idx
										1 +to file-idx
										over entry-file-size @ len-buf idx cells + !
										names-buf idx 13 * + dup 13 bl fill
											12 3 pick file-name@ 2drop
										then
											date-buf idx 2* date-time-size * + 2 pick create-date-time@ 
											date-buf idx 2* 1+ date-time-size * + 2 pick modify-date-time@ 
											idx sort-buf idx cells + !
										false
									else
										2drop true
									then
								until
						;] with-aligned-allot
					;] current-fs@ with-open-dir-at-root-path
				;] fs-lock with-lock
			then
			entries-count 0> if
				sorted if
								[: { offset n sort-buf names-buf }
									0 0 true { idx1 idx2 finish }
										n 1 > if
											begin 
												true to finish
												n 1 - 0 do  
													sort-buf i offset + cells + dup @ to idx1 cell + @ to idx2
													names-buf idx1 13 * + names-buf idx2 13 * + filenames> if
														idx2 sort-buf i offset + cells + !
														idx1 sort-buf i offset + 1+ cells + !
														false to finish
													then
												loop
											finish until
										then

								;] { bubble-sort }

					0 dir-count sort-buf names-buf bubble-sort execute
					dir-count entries-count dir-count - sort-buf names-buf bubble-sort execute

				then
				long if
								entries-count 0 do 
									names-buf sort-buf i cells + @ 13 * + 13 type \ name
									2 spaces
									sort-buf i cells + @ dir-count < if 
										." DIR  "
									else
										len-buf sort-buf i cells + @ cells + @ size-human-readable
									then
									dates if
										sort-buf i cells + @ 2* date-time-size * date-buf + date-time. space ." M:"
										sort-buf i cells + @ 2* 1+ date-time-size * date-buf + date-time. space
									then
									cr
								loop 
				else
								15 { col_width }
								term-cols @ col_width / dup 0= if drop 1 then { num_cols }
								entries-count num_cols / { num_rows }
								entries-count num_cols mod 0 > if 1 +to num_rows then
								\ correction
								entries-count num_rows / to num_cols
								entries-count num_rows mod 0 > if 1 +to num_cols then
								num_rows 0 do 
									num_cols 0 do 
										i num_rows * j + dup entries-count < if cells sort-buf + @ 13 * names-buf + 13 type 2 spaces else drop col_width spaces then
									loop cr
								loop
				then
				names-buf ram-here!
			then
			
		;

		: cd ( word -- )
			token
				dup 0= if  \ empty path = root
					2drop
					s" /"
				then
				fat32-tools::change-dir
		;

		256 buffer: rm-path
		variable rm-verbose
        variable rm-ptr
		
		: next-dir ( -- str n )
			rm-path @ 0> rm-ptr @ rm-path @ < and  if
				rm-path @ 0 do
					rm-path cell + i + rm-ptr @ + c@ [char] / = i rm-ptr @ + 0> and i rm-ptr @ + rm-path @ 1- >= or if
						i 1+ rm-ptr +!
						rm-path cell + rm-ptr @  leave
					then
				loop
			else
				0 0
			then
		;

		: mkdir ( word )
			cr
			token { tkn n }
			0 { parents }
			0 { p-end }
			begin 
			n 0> if
				tkn c@ [char] - = if
					tkn n [char] p char-in-string? if true to parents then
					tkn n [char] h char-in-string? if
						." mkdir [-p] <dir1> <dir2> ... " cr
						." -p: create parents" cr
						0 to n
					else
						token to n to tkn
					then
				else
					parents not if
						tkn n fat32-tools::create-dir
						token to n to tkn
					else
						tkn n rm-path string!
						0 rm-ptr !
						begin
							next-dir dup to p-end
							dup 0> if
								2dup fat32-tools::exists? not if
									fat32-tools::create-dir
								then
							then
						p-end 0= until
						token to n to tkn
					then
				then
			then
			n 0= until
		;
		
		: rm-path-add { str n -- }
			n 0> if
				rm-path @ { idx }
				rm-path cell + idx + 1- c@ [char] / = not idx 0> and if [char] / rm-path cell + idx + c! 1 +to idx then
				n 0 do
					str i + c@ rm-path cell + idx + i + c!
				loop
				[char] / rm-path cell + idx + n + c!
				idx n + 1 + rm-path !
			then
		;

		: rm-path-del ( -- )
			rm-path @ 2 > rm-path cell + rm-path @ [char] / char-in-string? and if
				0 rm-path @ 2 - do
					rm-path cell + i + c@ [char] / = if 
						i 1+ rm-path !
						leave
					then
					i 0= if
						rm-path cell + c@ [char] / = if
							s" /" rm-path string!
						else
							0 rm-path !
						then
					then
				-1 +loop

			else
						rm-path cell + c@ [char] / = if
							s" /" rm-path string!
						else
							0 rm-path !
						then

			then
		;

		: rm-path-str (  -- rm-path-adr rm-path-len  ) rm-path cell + rm-path @ ;

		defer rm-r ( path-adr path-n  -- ) \ recursive delete of dir
				
		:noname { tkn n }
			tkn n rm-path-add
			rm-path-str 1- + c@ [char] / = if rm-path-str 1- else rm-path-str then
			{ fn-adr fn-len }
			fn-adr fn-len fat32-tools::file? if
				rm-verbose @ if ." removing file: " fn-adr fn-len  type cr then
				fn-adr fn-len  fat32-tools::remove-file 
			else
				rm-path-str fat32-tools::dir? if
					rm-path-str dir-entries-num 0= if
						rm-verbose @ if ." removing directory: " rm-path-str type cr then
						rm-path-str fat32-tools::remove-dir
					else
						rm-path-str ['] rm-r for-each-in-dir
						rm-path-str fat32-tools::remove-dir
					then
				then
			then
			rm-path-del
		; is rm-r

		: rm ( word -- )
			current-fs@ averts x-fs-not-set
			cr
			token { tkn n }
			begin 
			n 0> if
				tkn c@ [char] - = if
					tkn n [char] R char-in-string? if
						tkn n [char] v char-in-string? rm-verbose !
						0 rm-path !
						token rm-r
						0 to n
					then
					tkn n [char] h char-in-string? n 0> and if
						." rm [-Rv] <dir or file> <dir or file>..." cr
						." -R : recursive deletion of one directory" cr
						." -v : verbose for recursive deletion " cr
						0 to n
					then
				else
					tkn n fat32-tools::dir? if
							tkn n fat32-tools::remove-dir
					else
						tkn n fat32-tools::file? if
							tkn n fat32-tools::remove-file
						then
					then
					token to n to tkn
				then
			then
			n 0= until
		;

	end-module> import

	' ls export ls
	' cd export cd
	' rm export rm
	' mkdir export mkdir

end-module

