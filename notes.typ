we want to optimize a multi output boolean network with 2 gate inputs. for $n$ inputs we have $n^2$ possible input states, and for $m$ outputs means we have a $n^2 -> m$ map. each function can be thought of as just 1 byte, {input, output} which are each $2^2$ bits. we want to build all realizable functions until we find one that matches, starting from simplest. this is quite inefficient but because we expect small input problems it shouldn't be too bad. by the way this means our entire function can be efficiently represented as just bits.

so for example if our input is just 2 bits, and we have 1 output, our output function is the same as 1 gate: 8 bits. we can view the application of an operator as a modification of the truth table, a simple composition. so this means for $k$ gates it's the same as limitng ourselves to $k$ compositions. we simply have to keep track of these compositions to know what gates we used to arrive at that solution. we can store the function itself as a bitset and store gates by their indices. so then to arrive at all realizable functions:

we know at each level k that we will never have an early stop so we only check for SAT at the end, which is simply checking equality between provided multi output truth table and our generated function

recursive function storing number of modifications (depth)
each time we iterate through all available gates
  iterate through all possible applications of the function (all possible compositions on the table)
    recurse


improved algorithm consists of:
for cost c:
  split into c_1, c_2 + 1:
    for op in operators:
      for a in frontier[c_1]:
        for b in frontier[c_2]:
          compute h = op(a, b)
          update best_cost[h], witness[h], add to frontier[c], if needed. no point in adding to frontier if a better version with the same output exists already, right?

stop once the required input functions are in best cost

so what does this actually do? so for c = 0 we just add all the inputs as truth tables.
for c = 1, we can compose 0 cost things, so that means to frontier[1] we add all the functions that can be constructed with the operators from the inputs. this would also populate best_cost with the best ways to obtain new outputs. we can represent best cost as integer max value for gates that we haven't realized yet.

this means once best cost contains all the output functions we want, we're done. 
