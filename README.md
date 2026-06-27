# Roblox_Internal_Plugin_Decoder
Decodes Roblox's internal roblox studio plugin models. and also decompiles them. (with a custom luau decompiler made in python)  
  
These plugins can be found in <rbxstudio>/BuiltInPlugins and <rbxstudio>/BuiltInStandalonePlugins respectively.  
You're not supposed to be able to view these plugin's content usually.  
But they're just normal RBXM files with a stupid gimmick; it uses compiled bytecode as the source of plugins.  
This makes it impossible to load it up normally in Roblox Studio.  
However this decoder makes it so the RBXM file gets translated into RBXMX (roblox's xml model format).  

#How to use  
download the zip  
you need python. (and any other packages it might talk about)  
you need the plugin you want to decode to be in the same folder as the script.  
normally, if you just do ```python recom.py <plugin>.rbxm```  
it'll disassemble the code rather than decompile.  
if you want to do decompile the code (which might also be a bit slower)  
put in the flag --decode  
and if you want to extract the bytecode you gotta do --sources <foldername>  
and (hopefully) it should work.  
also dw if the decompiler (or disassembler) fails, it wont stop the main script.  
  
#legal stuff  
if roblox wants me to take this down, i'll take this down since i dont want any issues with the roblox legal team.  
