# Thesis_SIDH_CRS

Accompanying code for my thesis about "Cryptanalysis of an isogeny-based system and its applications".

## Attack on SIDH 

To run the attack on SIDH, run [``SIKE_break.m``](SIKE_break.m): 
  - One can choose the parameters by uncommenting the respective line in the beginning of the file.
  - By default the file [``richelot_formulae_strategy.m``](richelot_formulae_strategy.m) is loaded, you can change this by loading  [``richelot_formulae.m``](richelot_formulae.m) in order to run the attack without the optimal strategies.
 
 
## Attack on weak instances of CRS 

To run the attack on CRS, run [``WeakInstancesCRS.m``](WeakInstancesCRS.m): 
 - If you get an assertion error, then this is because the wrong &#956; was chosen. Running the attack a couple of times solves this.
 - (Un)comment line 339-334 to choose if you want to run ``example1()`` or ``example2()``. 

