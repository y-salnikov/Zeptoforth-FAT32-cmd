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

			long sorted dates
			tkn n
			[:
				[:
					<fat32-dir> class-size [: 
						 2dup swap clone-dir
						<fat32-entry> class-size [:
						0 0 { long sorted dates dir dir_ entry entries-count dir-count }
						entry dir_
						begin
							2dup read-dir if
									1 +to entries-count
									over entry-dir? if 1 +to dir-count then
									false
							else
								2drop true
							then
						until
						ram-here { names-buf }
						entries-count 13 * ram-allot
						4 ram-align,
						ram-here { sort-buf }
						entries-count cells ram-allot
						ram-here { len-buf }
						entries-count cells  ram-allot
						ram-here { date-buf }
						entries-count date-time-size 2* * ram-allot 4 ram-align,
						
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
								entries-count num_cols mod num_cols 2/ >= if 1 +to num_rows then
								\ correction
								entries-count num_rows / to num_cols
								entries-count num_rows mod num_rows 2/ >= if 1 +to num_cols then
								num_rows 0 do 
									num_cols 0 do 
										i num_rows * j + dup entries-count < if cells sort-buf + @ 13 * names-buf + 13 type 2 spaces else drop col_width spaces then
									loop cr
								loop
							then
						then
						;] with-aligned-allot
					;] with-aligned-allot
				;] current-fs@ with-open-dir-at-root-path
			;] fs-lock with-lock
		;

		: cd ( word -- )
			token
				dup 0= if  \ empty path = root
					2drop
					s" /"
				then
				fat32-tools::change-dir
		;

		: mkdir ( word ) \ todo: -p option
			cr
			token { tkn n }
			begin 
			n 0> if
				tkn c@ [char] - = if
					token to n to tkn
				else
					tkn n fat32-tools::create-dir
					token to n to tkn
				then
			then
			n 0= until
		;
		
		defer rm-r ( path-adr path-n  -- ) \ recursive delete of dir
				
		:noname
					\ todo:
		; is rm-r

		: rm ( word -- )
			current-fs@ averts x-fs-not-set
			cr
			token { tkn n }
			begin 
			n 0> if
				tkn c@ [char] - = if
					tkn n [char] R char-in-string? if
						token rm-r
						0 to n
					then
					tkn n [char] h char-in-string? if
						." rm [-R] <dir or file> <dir or file>..." cr
						." -R : recursive deletion of one directory" cr
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

