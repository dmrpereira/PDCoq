theplug_MLLIB_DEPENDENCIES:= coq_lib plugin
theplug.cma:$(addsuffix .cmo,$(theplug_MLLIB_DEPENDENCIES))
theplug.cmxa theplug.cmxs:$(addsuffix .cmx,$(theplug_MLLIB_DEPENDENCIES))
