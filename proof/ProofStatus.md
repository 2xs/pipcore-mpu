# Proof Status

| System call    	| Security properties 	| Consistency properties 	| Other 	|   	|
|----------------	|---------------------	|:----------------------:	|:-----:	|---	|
| findBlock      	| 100%                	| 100%                   	| 100%  	|   	|
| readMPU        	| 100%                	| 100%                   	| 100%  	|   	|
| addMemoryBlock 	| 100%                	| 100%                   	| 100%  	|   	|

# Git proof branches
There is one git branch per service that holds the proof of that service **only**.
All proofs were brought to the first write instruction, *i.e.* after the check phase of the service.
This has been done to reveal as many consistency properties as possible, and reduce the likelihood to pass over the proofs again later on.
The corresponding git proof branch to the service holds the current proof status.

As soon as a major step has been achived in a proof of a service (for example end of the check phase, reusable lemmas, end of proof), the modifications are pushed to the *common_lemmas* branch and propagated to all git proof branches.
Once the proof of a service is done, it is merged into *common_lemmas*, propagated to all other git proof branches, merged into the *master* branch, and the branch is finally deleted.