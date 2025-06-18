note
    model: second, minute, hour
class

	TIME_1
create
	make, make_2
feature {NONE}
	second: INTEGER
	minute: INTEGER
	hour: INTEGER

	make
		note
			status: creator
		do
			hour := 23
			minute := 59
			second := 59
		ensure
			hour_is_23: hour = 23
			minute_is_59: minute = 59
			second_is_59: second = 59
		end

	make_2 (a_hour, a_minute, a_second: INTEGER)
		note
			status: creator
		require
			a_hour_within_bounds: 0 <= a_hour and a_hour < 24
			a_minute_within_bounds: 0 <= a_minute and a_minute < 60
			a_second_within_bounds: 0 <= a_second and a_second < 60
		do
			hour := a_hour
			minute := a_minute
			second := a_second
		ensure
			hour_is_a_hour: hour = a_hour
			minute_is_a_minute: minute = a_minute
			second_is_a_second: second = a_second
		end
feature

	set_second (a_second: INTEGER)
		require
			a_second_within_bounds: 0 <= a_second and a_second < 60
		do
			second := a_second
		ensure
			modify_model ("second", Current)
			second_is_a_second: second = a_second
		end

	set_minute (a_minute: INTEGER)
		require
			a_minute_within_bounds: 0 <= a_minute and a_minute < 60
		do
			minute := a_minute
		ensure
			modify_model ("minute", Current)
			minute_is_a_minute: minute = a_minute
		end

	buggy_set_hour (a_hour: INTEGER)
		require
			is_wrapped: is_wrapped
			a_hour_within_bounds: 0 <= a_hour and a_hour <= 24
		do
			hour := a_hour
		ensure
			is_wrapped: is_wrapped
			modify_model ("hour", Current)
			hour_is_a_hour: hour = a_hour
		end

	get_time: TIME_1
		do
			Result := create {TIME_1}.make_2 (hour, minute, second)
		ensure
			result_is_object_equal_to_current: hour = Result.get_hour and minute = Result.get_minute and second = Result.get_second
			result_is_not_current: Result /= Current
		end

	get_second: INTEGER
		do
			Result := second
		ensure
			result_is_second: Result = second
		end

	get_minute: INTEGER
		note
			status: functional
		do
			Result := minute
		end

	get_hour: INTEGER
		do
			Result := hour
		ensure
			result_is_hour: Result = hour
		end

	convert_to_seconds: INTEGER
		do
			Result := hour * 60 * 60 + minute * 60 + second
		ensure
			result_in_seconds: Result = hour * 60 * 60 + minute * 60 + second
		end

	decr
		note
			explicit: wrapping, contracts
		require
			is_wrapped: is_wrapped
		do
			if not is_time_zero then
				unwrap
				second := second - 1
				if second < 0 then
					second := 59
					minute := minute - 1
					if minute < 0 then
						minute := 59
						hour := hour - 1
						-- if hour < 0 then
						-- 	hour := 23
						-- end
					end
				end
				wrap
			end
		ensure
			modify_model ("second", Current)
			modify_model ("minute", Current)
			modify_model ("hour", Current)
			is_wrapped: is_wrapped
			if_convert_to_second_is_0: old convert_to_seconds = 0 implies convert_to_seconds = 0
			if_convert_to_second_is_not_0: old convert_to_seconds /= 0 implies convert_to_seconds = old convert_to_seconds - 1
		end

	timer
		note
			explicit: wrapping, contracts
		require
			is_wrapped: is_wrapped
		do
			from
			invariant
				is_wrapped: is_wrapped
			until
				is_time_zero
			loop
				decr
			variant
				convert_to_seconds
			end
		ensure
			modify_model ("second", Current)
			modify_model ("minute", Current)
			modify_model ("hour", Current)
			is_wrapped: is_wrapped
			convert_to_second_is_0: convert_to_seconds = 0
		end

	timer_2 (a_hour, a_minute, a_second: INTEGER)
		note
			explicit: wrapping, contracts
		require
			is_wrapped: is_wrapped
			a_hour_within_bounds: 0 <= a_hour and a_hour < 24
			a_minute_within_bounds: 0 <= a_minute and a_minute < 60
			a_second_within_bounds: 0 <= a_second and a_second < 60
		do
			buggy_set_hour (a_hour)
			set_minute (a_minute)
			set_second (a_second)
			check assignment: hour = a_hour and minute = a_minute and second = a_second end
			timer
		ensure
			is_wrapped: is_wrapped
			modify_model ("second", Current)
			modify_model ("minute", Current)
			modify_model ("hour", Current)
			convert_to_second_is_0: convert_to_seconds = 0
		end

	is_time_zero: BOOLEAN
		require
			is_wrapped: is_wrapped
		do
			Result := (convert_to_seconds = 0)
		ensure
			is_wrapped: is_wrapped
			result_is_time_zero: Result = (convert_to_seconds = 0)
		end

	reset
		do
			hour := 0
			minute := 0
			second := 0
		ensure
			modify_model ("second", Current)
			modify_model ("minute", Current)
			modify_model ("hour", Current)
			hour_is_0: hour = 0
			minute_is_0: minute = 0
			second_is_0: second = 0
		end

	later_than (a_time: TIME_1): BOOLEAN
		do
			if hour /= a_time.get_hour then
				Result := hour > a_time.get_hour
			elseif minute /= a_time.get_minute then
				Result := minute > a_time.get_minute
			else
				Result := second > a_time.get_second
			end
		ensure
			is_later_than_a_time: Result = (hour > a_time.get_hour or
			(hour = a_time.get_hour and (minute > a_time.get_minute)) or
			(hour = a_time.get_hour and minute = a_time.get_minute and second > a_time.get_second))
		end

	equals (a_object: ANY): BOOLEAN
		-- note
		-- 	status: functional
		do
			Result := if attached {TIME_1} a_object as a_time then
				(hour = a_time.get_hour and minute = a_time.get_minute and second = a_time.get_second)
			else
				False
			end
		ensure
			a_object_not_time: not attached {TIME_1} a_object as a_time implies Result = False
			a_object_is_time: attached {TIME_1} a_object as a_time implies Result = (hour = a_time.get_hour and minute = a_time.get_minute and second = a_time.get_second)
		end
feature {NONE} -- Ghost variables

	stop_minute (a_start, a_stop: TIME_1): INTEGER
		note
			status: functional, ghost
			explicit: wrapping, contracts
		require
			a_start_is_wrapped: a_start.is_wrapped
			a_stop_is_wrapped: a_stop.is_wrapped
		do
			Result := if a_stop.get_second < a_start.get_second then
				a_stop.get_minute - 1
			else
				a_stop.get_minute
			end
		ensure
			a_start_is_wrapped: a_start.is_wrapped
			a_stop_is_wrapped: a_stop.is_wrapped
		end
	stop_hour (a_start, a_stop: TIME_1): INTEGER
		note
			status: functional, ghost
			explicit: wrapping, contracts
		require
			a_start_is_wrapped: a_start.is_wrapped
			a_stop_is_wrapped: a_stop.is_wrapped
		do
			Result := if stop_minute (a_start, a_stop) < a_start.get_minute then
				a_stop.get_hour - 1
			else
				a_stop.get_hour
			end
		ensure
			a_start_is_wrapped: a_start.is_wrapped
			a_stop_is_wrapped: a_stop.is_wrapped
		end

	diff_hour (a_start, a_stop: TIME_1): INTEGER
		note
			status: functional, ghost
			explicit: wrapping, contracts
		require
			a_start_is_wrapped: a_start.is_wrapped
			a_stop_is_wrapped: a_stop.is_wrapped
		do
			Result := stop_hour (a_start, a_stop) - a_start.get_hour
		ensure
			a_start_is_wrapped: a_start.is_wrapped
			a_stop_is_wrapped: a_stop.is_wrapped
		end

	diff_minute (a_start, a_stop: TIME_1): INTEGER
		note
			status: functional, ghost
			explicit: wrapping, contracts
		require
			a_start_is_wrapped: a_start.is_wrapped
			a_stop_is_wrapped: a_stop.is_wrapped
		do
			Result := if stop_minute (a_start, a_stop) < a_start.get_minute then
				stop_minute (a_start, a_stop) + 60 - a_start.get_minute
			else
				stop_minute (a_start, a_stop) - a_start.get_minute
			end
		ensure
			a_start_is_wrapped: a_start.is_wrapped
			a_stop_is_wrapped: a_stop.is_wrapped
		end

	diff_second (a_start, a_stop: TIME_1): INTEGER
		note
			status: functional, ghost
			explicit: wrapping, contracts
		require
			a_start_is_wrapped: a_start.is_wrapped
			a_stop_is_wrapped: a_stop.is_wrapped
		do
			Result := if a_stop.get_second < a_start.get_second then
				a_stop.get_second + 60 - a_start.get_second
			else
				a_stop.get_second - a_start.get_second
			end
		ensure
			a_start_is_wrapped: a_start.is_wrapped
			a_stop_is_wrapped: a_stop.is_wrapped
		end

feature 
	trusted_difference (a_start, a_stop: TIME_1): TIME_1
		note
			explicit: wrapping, contracts
		require
			a_start_is_wrapped: a_start.is_wrapped
			a_stop_is_wrapped: a_stop.is_wrapped
			a_stop_later_than_a_start: a_stop.later_than (a_start) or a_stop.equals (a_start)
		local
			l_diff: TIME_1
			l_tmp_second, l_tmp_minute, l_tmp_hour: INTEGER
		do
			l_diff := create {TIME_1}.make
			l_tmp_second := a_stop.get_second
			l_tmp_minute := a_stop.get_minute
			l_tmp_hour := a_stop.get_hour

			if l_tmp_second < a_start.get_second then
				l_tmp_minute := l_tmp_minute - 1
				l_tmp_second := l_tmp_second + 60
				check stop_minute: l_tmp_minute = stop_minute (a_start, a_stop) end
			end

			check stop_minute: l_tmp_minute = stop_minute (a_start, a_stop) end

			l_diff.set_second (l_tmp_second - a_start.get_second)

			if l_tmp_minute < a_start.get_minute then
				l_tmp_hour := l_tmp_hour - 1
				l_tmp_minute := l_tmp_minute + 60
			end

			l_diff.set_minute (l_tmp_minute - a_start.get_minute)
			l_diff.buggy_set_hour (l_tmp_hour - a_start.get_hour)

			Result := l_diff
		ensure
			diff_hour: Result.get_hour = diff_hour (a_start, a_stop)
			diff_minute: Result.get_minute = diff_minute (a_start, a_stop)
			diff_second: Result.get_second = diff_second (a_start, a_stop)
		end

	difference (a_start, a_stop: TIME_1): TIME_1
		note
			explicit: wrapping, contracts
		require
			a_start_is_wrapped: a_start.is_wrapped
			a_stop_is_wrapped: a_stop.is_wrapped
			req: a_stop.later_than (a_start) or a_start.later_than (a_stop) or a_stop.equals (a_start)
		do
			Result := if a_stop.later_than (a_start) then
				trusted_difference (a_start, a_stop)
			else
				trusted_difference (a_stop, a_start)
			end
		ensure
			a_stop_gt_a_start: a_stop.later_than (a_start) implies (Result.get_hour = (trusted_difference (a_start, a_stop)).get_hour and Result.get_minute = (trusted_difference (a_start, a_stop)).get_minute and Result.get_second = (trusted_difference (a_start, a_stop)).get_second)
		end

	time_options (a_start, a_stop: TIME_1; a_sel: INTEGER): TIME_1
		note
			status: impure
			explicit: wrapping, contracts
		require
			is_wrapped: is_wrapped
			a_start_is_wrapped: a_start.is_wrapped
			a_stop_is_wrapped: a_stop.is_wrapped
			a_sel_within_bounds: 0 <= a_sel and a_sel < 5
		do
			if a_sel = 0 then
				reset
			elseif a_sel = 1 then
				timer_2 (a_start.get_hour, a_start.get_minute, a_start.get_second)
			elseif a_sel = 2 then
				timer
			elseif a_sel = 3 then
				if a_start.equals (a_stop) then
					a_start.reset
					Result := a_start.get_time
				end
			else
				Result := difference (a_start, a_stop)
			end

			if Result = Void then
				Result := get_time
			end
		ensure
			modify (a_start, Current)
			a_sel_0_1_2: (0 <= a_sel and a_sel <= 2) implies (Result.get_hour = 0 and Result.get_minute = 0 and Result.get_second = 0 and a_start = old a_start and a_stop = old a_stop)
			a_sel_3_a_start_neq_a_stop: ((a_sel = 3 and (not (a_start.equals (old a_stop)).old_)) implies (Result.get_hour = hour and Result.get_minute = minute and Result.get_second = second)) 
			a_sel_3_a_start_eq_a_stop: ((a_sel = 3 and ((a_start.equals (old a_stop)).old_)) implies (Result.get_hour = 0 and Result.get_minute = 0 and Result.get_second = 0 and a_start.get_hour = 0 and a_start.get_minute = 0 and a_start.get_second = 0 and a_stop = old a_stop)) 
			a_sel_4: a_sel = 4 implies (Result.get_hour = difference (a_start, a_stop).get_hour and Result.get_minute = difference (a_start, a_stop).get_minute and Result.get_second = difference (a_start, a_stop).get_second and a_start = old a_start and a_stop = old a_stop)
		end

invariant
	second_within_bounds: 0 <= second and second < 60
	minute_within_bounds: 0 <= minute and minute < 60
	hour_within_bounds: 0 <= hour and hour < 24
end
