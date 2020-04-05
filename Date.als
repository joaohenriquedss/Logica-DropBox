module Date

sig Date {
	
}
sig Day {
	hours : one Hour
}

sig Hour {
	minutes : one Minute
}
sig Minute {
}

-- Fato

fact {

--	all d:Day | one d.~day  -- Todo dia deve pertencer a uma Data
	all h:Hour | one h.~hours  -- Toda hora deve pertencer a um Dia 
	all m:Minute | one m.~minutes -- Todo minuto deve pertencer a uma Hora

}
