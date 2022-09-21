The .m files contain magma code expressing the optimized radical isogeny formulae for N<20.
The folder 'formulae' contains complete radical isogeny formulae for all prime powers 16<N<30.
The subfolders newA and newB list separately the coefficients of alpha^d in the expressions for A' and B' respectively.
Here alpha denotes an N-th root of the radicand gamma_1/(N^2*b)^N, where gamma_1 is as in the paper.
The file d.sage corresponds to the coefficient of \alpha^d, and the value of this coefficient is num/den, where num and den are as in the file.

The folder 'code' contains the SageMath scripts used to obtain these formulae.

Instructions to use the scripts:
- specify all parameters followed by a # in make_samples/gen.sage
- run code/make_samples/gen.sage
- specify all parameters followed by a # in interpolate/gen.sage
- run code/interpolate/gen.sage