# Frontend route correction

The runner for job 53333815 clears KM variables and invokes km ofn without KM_ROUTE. Code inspection confirms that standalone ofn defaults to manual; the earlier automatic label was incorrect. Its measurements remain unchanged and now describe standalone default/manual frontend equivalence.

check_iri_frontend_auto.py sets KM_ROUTE=auto explicitly in both arms and otherwise preserves the same frozen inputs, binary, limits and exact output comparison. The separate full run covers the automatic frontend used by classification. The default/manual run is retained with all failures. No completed or live measurement is overwritten.
