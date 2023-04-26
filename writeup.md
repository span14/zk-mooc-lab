# Abstract
Sha2-256 circuit implementation relies on the design of 16bit table chip brought up by [zcash](https://zcash.github.io/halo2/design/gadgets/sha256/table16.html). It teaches me what lookup means in the circuit and gives hint on ripemd160 and blake2f that are WIP.

# SHA2
There two phases in the circuit: Message Scheduling and Compression. They are arranged as two different subregions. 

## Message Scheduling
Message Scheduling is about three formulas:

$\sigma_{0}=(X>>>7)\oplus(X>>>18)\oplus(X>>3)$

$\sigma_{1}=(X>>>17)\oplus(X>>>19)\oplus(X>>10)$

$W_{i}=\sigma_{0}(W_{i-2})+W_{i-7}+\sigma_{1}(W_{i-15})+W_{i-16}$

Addition output should modulo $2^{32}$ in order to keep $W_{i}$ as a 32 bit number. Contraining $W_i$ is relatively easier here because what we need to do is to constrain the result of $W_i$ + Carry of $W_i$ * $2^{32}$ is the output of above formular as well as the size of the Carry value(<4)

$\sigma_{0}$ and $\sigma_{1}$ need to use the trick of spread table. Spread table defines a tag and spread form of a value with size less than 17 bits. Tag here indicates the bit size range of the value. For example, in the spread table we use here, value that has size of less than 7 bits, the tag is 0. And spread form of a number is to add bit 0 afront of each bit in the value to expand it into 32 bit. For example, the spread form of *0b0000011111111111* is *0b00000000010101010101010101010101*.

What is essential is that the right rotation shift in $\sigma$ functions involves decomposing $W_{i}$ and tag is used to restrict the size of decomposed components. The spread form trick can simulate various bitwise operations by adding different combination of even/odd bits of $M$ where spread form of $M$ is the addition result of the spread form of bitwise operation participants. In the meantime, even/odd bits of $M$ follows the rule that $Spread(M_{e}) + Spread(M_{o}) * 2 = Spread(M)$. 

## Compression
Compression subregion also utilizes the same techniques in message scheduling sections. The details of required operations can be found in [zcash](https://zcash.github.io/halo2/design/gadgets/sha256/table16.html).

## Miscellaneous
Inside implementation, except for inputs and first round of initial $H$ values in message scheduling phase, there are a lot of copy constraint needed and these constraints increase the equality gadget in Halo2. I am not sure if that's the correct way to write the circuits. 



