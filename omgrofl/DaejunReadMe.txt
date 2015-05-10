Hey Daejun, 

I am nearing the end of my work on implementing OmgRofl in K, and would like some 
input to make sure what I have done is sufficient or how I can improve.

Some of the features defined in http://esolangs.org/wiki/omgrofl are tricky
to implement in K and wanted some advice.

Notable the things I had to change was:
* for loops changed from 
4 variable iz initial-value 2 end-value
to 
4 variable iz initial-value 2lmfao end-value
as K was complaining about 2 being a reserved keyword.

* Printing to stdout
rofl Exp
to 
lulz Exp
K was getting confused with rofl and roflmao and I couldn't devise a solution

Some things I couldn't get working were
* Comments being defined by w00t till end of line as there is no real end of line
delimeter
* sleep() like function called afk in omgrofl that has a program sleep for
for some amount of time

MOST IMPORTANT
* I can't come up with a way to use a regex like lo^l as my variable names
(thats all thats allowed in omgrofl) so I am currently using Id, is there a 
simple solution?