theory CabineTemperature
  imports ARINC_661

begin

value*[TemperatureCelciusScale::Picture, widget_ident=4642,parent_ident="Some 4641"]
\<open>@{Picture \<open>TemperatureCelciusScale\<close>}\<close>
value*[TemperatureIndicatedPointer::Symbol, widget_ident=4643,parent_ident="Some 4641"]
\<open>@{Symbol \<open>TemperatureIndicatedPointer\<close>}\<close>
value*[TemperatureSelectedPointer::Symbol, widget_ident=4644,parent_ident="Some 4641"]
\<open>@{Symbol \<open>TemperatureSelectedPointer\<close>}\<close>
value*[IndicatedTempDRO::Label, widget_ident=4645,parent_ident="Some 4641", label_string="\<open>24\<close>"]
\<open>@{Label \<open>IndicatedTempDRO\<close>}\<close>
value*[IndicatedUnitLabel::Label, widget_ident=4645,parent_ident="Some 4641", label_string="\<open>C\<close>"]
\<open>@{Label \<open>IndicatedUnitLabel\<close>}\<close>
value*[IncreaseSelectTemp::PicturePushButton, widget_ident=4646,parent_ident="Some 4641"]
\<open>@{PicturePushButton \<open>IncreaseSelectTemp\<close>}\<close>
value*[DecreaseSelectTemp::PicturePushButton, widget_ident=4647,parent_ident="Some 4641"]
\<open>@{PicturePushButton \<open>DecreaseSelectTemp\<close>}\<close>

value*[CabinTempPanel::Panel, widget_ident=4641]
\<open>@{Panel \<open>CabinTempPanel\<close>}\<close>

value*[Layer66::Layer, layer_id=66, widgets_tree="{CabinTempPanel, DecreaseSelectTemp, IncreaseSelectTemp, IndicatedUnitLabel, IndicatedTempDRO, TemperatureSelectedPointer, TemperatureIndicatedPointer, TemperatureCelciusScale}"]
\<open>@{Layer \<open>Layer66\<close>}\<close>

value*[CabineTemperature::Window, application_id="0x6788", contained_layers="{@{Layer \<open>Layer66\<close>}}"]
\<open>@{Window \<open>CabineTemperature\<close>}\<close>

end