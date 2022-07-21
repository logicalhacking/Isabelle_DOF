theory ARINC_661
  imports  "Isabelle_DOF.technical_report"

begin

datatype Alignment = 
                     A661_BOTTOM_CENTER 
                   | A661_BOTTOM_LEFT 
                   | A661_BOTTOM_RIGHT 
                   | A661_CENTER 
                   | A661_LEFT
                   | A661_RIGHT 
                   | A661_TOP_CENTER 
                   | A661_TOP_LEFT 
                   | A661_TOP_RIGHT

datatype WidgetType = 
                  (* Containers *) 
                    A661_PANEL        
                  | A661_BASIC_CONTAINER 
                  | A661_BLINKING_CONTAINER
                  | MutuallyExclusiveContainer 
                  | TranslationContainer 
                  | RotationContainer 
                  | BlinkingContainer 
                  | TabbedPanelGroup 
                  | TabbedPanel 
                  | ScrollPanel 
                  (* Graphic widgets  *)
                  | A661_ACTIVE_AREA
                  | A661_LABEL 
                  | LabelComplex
                  (* Interactive widgets *)
                  | PushButton 
                  | ToggleButton 
                  | EditBoxNumeric 
                  | CheckButton 
                  | ComboBox 
                  (* Map widgets *)
                  | MapHorz
                  (* Utility widgets *)
                  | Connector
                  | A661_PICTURE
                  | A661_SYMBOL
                  | A661_PICTURE_PUSH_BUTTON

doc_class Widget =
          name  :: string
          widget_type  :: WidgetType
          widget_ident :: int
          parent_ident :: "int option"

doc_class Layer =
          name            :: string
          layer_id        :: int
          context_number  :: int
          height          :: int
          width           :: int
          visible         :: bool
          enable          :: bool
          widgets_tree    :: "Widget set"

(* invariant : When a layer becomes inactive, its visibility is turned off 
by the CDS (an exception to this is when a NoServiceMonitor widget is present in the layer; *)

doc_class Window =
          application_id   :: int
          height           :: int
          width            :: int
          be_resized       :: bool <= True
          contained_layers :: "Layer set"
          type_synonym DefinitionFile = Window
          type_synonym DF = DefinitionFile

doc_class DisplayUnit = 
          contained_windows :: "Window set"
          type_synonym DU = DisplayUnit
          type_synonym UserApplication = DisplayUnit
          type_synonym UA = UserApplication

section\<open>WIDGET LIBRARY\<close>

text\<open>The ActiveArea is transparent rectangular widget. 
The ActiveArea may have a graphical representation when this widget is highlighted 
or when it has the focus. A selection of this widget by a crew member initiates 
an event notification sent to the owner UA of the widget. \<close>

doc_class ActiveArea = Widget +
          widget_type           :: WidgetType <= A661_ACTIVE_AREA
          visible               :: bool
          enable                :: bool
          (* style_set :: ? *)
          pos_x                 :: int
          pos_y                 :: int
          size_x                :: int
          size_y                :: int
          next_focused_widget   :: int
          (* automatic_focus_motion :: ? Automatic motion of the focus on widget specified in NextFocusedWidget parameter *)
          EntryValidation       :: bool
          (* Indicator notifying the CDS that the UA has completed processing the entry or selection event. This flag also indicates the results of that processing *)
          invariant force_widget_type_1 :: "widget_type \<sigma> = A661_ACTIVE_AREA"

text\<open>The BasicContainer has no graphical representation. Its purpose is to group children widgets 
and to provide a means for managing the visibility and the interactivity of this set of widgets. 
The contained widgets are positioned with respect to the PosX, PosY of the BasicContainer. 
The position of the BasicContainer can be changed at run-time.\<close>

doc_class BasicContainer = Widget +
          widget_type           :: WidgetType <= A661_BASIC_CONTAINER
          visible               :: bool
          enable                :: bool
          pos_x                 :: int
          pos_y                 :: int
          invariant force_widget_type_2 :: "widget_type \<sigma> = A661_BASIC_CONTAINER"

text\<open>A BlinkingContainer is intended to apply blinking behavior to a group of widgets.\<close>

doc_class BlinkingContainer  = Widget +
          widget_type           :: WidgetType <= A661_BLINKING_CONTAINER
          visible               :: bool
          blinking_type         :: int (* Type of blinking (appearance to be defined by the aircraft OEM). Value of zero means no blinking. The definition of all other 255 values is determined by OEM. *)
          invariant force_widget_type_3 :: "widget_type \<sigma> = A661_BLINKING_CONTAINER"

text\<open>A Panel widget groups several widgets together in a rectangular area with clipping capabilities. 
Widgets placed within a Panel widget have their coordinates referenced to the PosX, PosY 
reference point of the Panel.\<close>

doc_class Panel = Widget +
          widget_type           :: WidgetType <= A661_PANEL
          visible               :: bool
          enable                :: bool
          (* style_set :: ? *)
          pos_x                 :: int
          pos_y                 :: int
          size_x                :: int
          size_y                :: int
          (* TO BE COMPLETED *)
          (* ADDED PROP *)
          contained_widgets     :: "Widget set"
          invariant force_widget_type_5 :: "widget_type \<sigma> = A661_PANEL"
          
text\<open>A Label widget consists of a text field at a defined display location. If the label is anonymous, 
it cannot be modified at runtime by the UA. If it is not anonymous, it can be modified by the UA\<close>

doc_class Label = Widget +
          widget_type           :: WidgetType <= A661_LABEL
          visible               :: bool
          anonymous             :: bool
          (* style_set :: ? *)
          pos_x                 :: int
          pos_y                 :: int
          size_x                :: int
          size_y                :: int
          label_string          :: string
          max_string_length     :: int
          alignement            :: Alignment
          (* TO BE COMPLETED *)
          invariant force_widget_type_4 :: "widget_type \<sigma> = A661_LABEL"


text\<open>A Picture widget is a reference to an image available in the CDS. 
The Picture reference can be modified by the UA\<close>

doc_class Picture = Widget +
          widget_type           :: WidgetType <= A661_PICTURE
          visible               :: bool
          anonymous             :: bool
          (* style_set :: ? *)
          pos_x                 :: int
          pos_y                 :: int
          size_x                :: int
          size_y                :: int
          (* picture_reference :: ? *)
          (* TO BE COMPLETED *)
          invariant force_widget_type_6 :: "widget_type \<sigma> = A661_PICTURE"

text\<open>The Symbol widget is similar to the Label widget, except it does not have a Max-String-Length 
parameter and the string parameter is replaced by a Symbol- Reference parameter (outside reference).\<close>

doc_class Symbol = Widget +
          widget_type           :: WidgetType <= A661_SYMBOL
          visible               :: bool
          anonymous             :: bool
          (* style_set :: ? *)
          pos_x                 :: int
          pos_y                 :: int
          (* TO BE COMPLETED *)
          invariant force_widget_type_7 :: "widget_type \<sigma> = A661_SYMBOL"

text\<open>A PicturePushButton widget is a PushButton including a picture and possibly a string.\<close>

doc_class PicturePushButton = Widget +
          widget_type           :: WidgetType <= A661_PICTURE_PUSH_BUTTON
          visible               :: bool
          enable                :: bool
          anonymous             :: bool
          (* style_set :: ? *)
          pos_x                 :: int
          pos_y                 :: int
          size_x                :: int
          size_y                :: int
          (* picture_reference :: ? *)
          (* TO BE COMPLETED *)
          invariant force_widget_type_8 :: "widget_type \<sigma> = A661_PICTURE_PUSH_BUTTON"

end
