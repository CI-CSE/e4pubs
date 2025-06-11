class
    PRIME_CHECK_8
feature

	buggy_is_prime (a: INTEGER): BOOLEAN
		require
			num_is_big_enough: 1 < a
		local
			i, mid: INTEGER
		do
			Result := True
			from
				i := 2
				mid := a // 2
			invariant
				i_in_range: 1 < i and i <= mid + 1
				not_missed: 2 < i implies across 2 |..| (i - 1) as k all a \\ k /= 0 end
				stops_when_found: not Result implies a \\ i = 0
				stops_early_enogh: not Result implies i <= mid

			until
				i > mid
			loop
				if a \\ i = 0 then
					Result := False
				else
					i := i + 1
				end
			variant
				{INTEGER}.max_value - i - if Result then 0 else 1 end
			end
		ensure
			if_prime: Result implies across 2 |..| (a // 2) as k all a \\ k /= 0 end
			if_not_prime: not Result implies (across 2 |..| (a // 2) as k some a \\ k = 0 end)
		end

end
