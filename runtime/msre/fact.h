#ifndef MSRE_FACT_H
#define MSRE_FACT_H

#include "misc.h"

struct BaseFact: public Pretty {
	virtual int node_id() = 0;
};

#endif /* MSRE_FACT_H */
