
theory Dunb imports Drc Dvars begin 

consts
  unb :: "string => cmdMeaning"

defs
  unb_def : "unb str state == 
    if state str = 0 then choice (assignv str ` (Suc ` UNIV)) state
    else if state str = 1 then {}
    else assignv str (state str - 1) state"

end

    
    

