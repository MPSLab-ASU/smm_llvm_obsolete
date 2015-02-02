//
//  Edge.cpp
//  gccfgProject
//
//  Created by Bryce Holton on 8/6/14.
//  Copyright (c) 2014 Bryce Holton. All rights reserved.
//

#include "Edge.h"

Edge::Edge()
{
    setConnectsTo(NULL);
    setNextEdge(NULL);
    setBackEdge(false);
    setPointerEdge(false);
}
Edge::~Edge()
{
    
}
