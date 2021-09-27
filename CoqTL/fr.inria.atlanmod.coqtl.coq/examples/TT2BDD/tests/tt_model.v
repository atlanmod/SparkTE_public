(********************************************************************
	@name Coq declarations for model
	@date 2020/12/16 11:35:32
	@description Automatically generated by XMI2Coq transformation.
 ********************************************************************)
		 
Require Import List.
Require Import core.Model.
Require Import String.
Require Import examples.TT2BDD.TT.


Definition InputModel : Model TTMetamodel_EObject TTMetamodel_ELink :=
	(Build_Model
		(
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "1771667101_Cell" "" true))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "702061917_Cell" "" true))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement PortEClass (Build_Abstract_Port InputPortEClass (BuildInputPort "1234250905_InputPort" "" "d")))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "726181440_Cell" "" true))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement TruthTableEClass (BuildTruthTable "460201727_TruthTable" "" "Test"))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "620557167_Cell" "" true))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "364639279_Cell" "" false))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "1806431167_Cell" "" false))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement RowEClass (BuildRow "865667596_Row" ""))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "63387985_Cell" "" true))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement PortEClass (Build_Abstract_Port InputPortEClass (BuildInputPort "812586739_InputPort" "" "a")))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "1810742349_Cell" "" true))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement RowEClass (BuildRow "769530879_Row" ""))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "1068586139_Cell" "" false))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "1866875501_Cell" "" false))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement RowEClass (BuildRow "1832532108_Row" ""))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "1306834002_Cell" "" true))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "1354083458_Cell" "" false))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement PortEClass (Build_Abstract_Port InputPortEClass (BuildInputPort "1881901842_InputPort" "" "b")))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "50699452_Cell" "" true))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "285133380_Cell" "" true))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "542365801_Cell" "" false))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "556488341_Cell" "" false))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement PortEClass (Build_Abstract_Port InputPortEClass (BuildInputPort "585324508_InputPort" "" "c")))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "1471086700_Cell" "" false))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "270095066_Cell" "" true))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "929383713_Cell" "" false))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "1270038388_Cell" "" true))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement RowEClass (BuildRow "2125062626_Row" ""))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "1292040526_Cell" "" true))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "574268151_Cell" "" true))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "1217875525_Cell" "" false))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "890545344_Cell" "" true))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "1813187653_Cell" "" false))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "510147134_Cell" "" false))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement PortEClass (Build_Abstract_Port OutputPortEClass (BuildOutputPort "16868310_OutputPort" "" "s")))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement RowEClass (BuildRow "245765246_Row" ""))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "48208774_Cell" "" false))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "1604002113_Cell" "" false))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement RowEClass (BuildRow "341138954_Row" ""))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "2051120548_Cell" "" true))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "1973233403_Cell" "" true))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement RowEClass (BuildRow "38262958_Row" ""))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "552936351_Cell" "" true))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "1427040229_Cell" "" false))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "1353530305_Cell" "" false))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "363509958_Cell" "" false))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "802243390_Cell" "" false))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "2033968586_Cell" "" false))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "1029472813_Cell" "" false))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "423583818_Cell" "" false))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "154319946_Cell" "" false))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "1787079037_Cell" "" true))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement RowEClass (BuildRow "13803304_Row" ""))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement RowEClass (BuildRow "71706941_Row" ""))) :: 
		nil)
		(
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "1771667101_Cell" "" true)  (BuildRow "71706941_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "1771667101_Cell" "" true)  (Build_Abstract_Port InputPortEClass  (BuildInputPort "812586739_Port" "" "a") ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "702061917_Cell" "" true)  (BuildRow "13803304_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "702061917_Cell" "" true)  (Build_Abstract_Port InputPortEClass  (BuildInputPort "1881901842_Port" "" "b") ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "726181440_Cell" "" true)  (BuildRow "245765246_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "726181440_Cell" "" true)  (Build_Abstract_Port InputPortEClass  (BuildInputPort "1881901842_Port" "" "b") ))) ::
		(Build_TTMetamodel_ELink TruthTablePortsEReference (BuildTruthTablePorts  (BuildTruthTable "460201727_TruthTable" "" "Test") ( (Build_Abstract_Port InputPortEClass  (BuildInputPort "812586739_Port" "" "a") ) ::  (Build_Abstract_Port InputPortEClass  (BuildInputPort "1881901842_Port" "" "b") ) ::  (Build_Abstract_Port InputPortEClass  (BuildInputPort "585324508_Port" "" "c") ) ::  (Build_Abstract_Port InputPortEClass  (BuildInputPort "1234250905_Port" "" "d") ) ::  (Build_Abstract_Port OutputPortEClass  (BuildOutputPort "16868310_Port" "" "s") ) :: nil ))) ::
		(Build_TTMetamodel_ELink TruthTableRowsEReference (BuildTruthTableRows  (BuildTruthTable "460201727_TruthTable" "" "Test") ( (BuildRow "769530879_Row" "") ::  (BuildRow "38262958_Row" "") ::  (BuildRow "1832532108_Row" "") ::  (BuildRow "13803304_Row" "") ::  (BuildRow "71706941_Row" "") ::  (BuildRow "865667596_Row" "") ::  (BuildRow "2125062626_Row" "") ::  (BuildRow "245765246_Row" "") ::  (BuildRow "341138954_Row" "") :: nil ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "620557167_Cell" "" true)  (BuildRow "2125062626_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "620557167_Cell" "" true)  (Build_Abstract_Port InputPortEClass  (BuildInputPort "812586739_Port" "" "a") ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "364639279_Cell" "" false)  (BuildRow "769530879_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "364639279_Cell" "" false)  (Build_Abstract_Port InputPortEClass  (BuildInputPort "812586739_Port" "" "a") ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "1806431167_Cell" "" false)  (BuildRow "865667596_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "1806431167_Cell" "" false)  (Build_Abstract_Port InputPortEClass  (BuildInputPort "1234250905_Port" "" "d") ))) ::
		(Build_TTMetamodel_ELink RowOwnerEReference (BuildRowOwner  (BuildRow "865667596_Row" "")  (BuildTruthTable "460201727_TruthTable" "" "Test"))) ::
		(Build_TTMetamodel_ELink RowCellsEReference (BuildRowCells  (BuildRow "865667596_Row" "") ( (BuildCell "1306834002_Cell" "" true) ::  (BuildCell "1354083458_Cell" "" false) ::  (BuildCell "270095066_Cell" "" true) ::  (BuildCell "1806431167_Cell" "" false) ::  (BuildCell "50699452_Cell" "" true) :: nil ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "63387985_Cell" "" true)  (BuildRow "341138954_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "63387985_Cell" "" true)  (Build_Abstract_Port InputPortEClass  (BuildInputPort "585324508_Port" "" "c") ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "1810742349_Cell" "" true)  (BuildRow "1832532108_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "1810742349_Cell" "" true)  (Build_Abstract_Port InputPortEClass  (BuildInputPort "1234250905_Port" "" "d") ))) ::
		(Build_TTMetamodel_ELink RowOwnerEReference (BuildRowOwner  (BuildRow "769530879_Row" "")  (BuildTruthTable "460201727_TruthTable" "" "Test"))) ::
		(Build_TTMetamodel_ELink RowCellsEReference (BuildRowCells  (BuildRow "769530879_Row" "") ( (BuildCell "364639279_Cell" "" false) ::  (BuildCell "1427040229_Cell" "" false) ::  (BuildCell "1604002113_Cell" "" false) :: nil ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "1068586139_Cell" "" false)  (BuildRow "2125062626_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "1068586139_Cell" "" false)  (Build_Abstract_Port OutputPortEClass  (BuildOutputPort "16868310_Port" "" "s") ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "1866875501_Cell" "" false)  (BuildRow "341138954_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "1866875501_Cell" "" false)  (Build_Abstract_Port OutputPortEClass  (BuildOutputPort "16868310_Port" "" "s") ))) ::
		(Build_TTMetamodel_ELink RowOwnerEReference (BuildRowOwner  (BuildRow "1832532108_Row" "")  (BuildTruthTable "460201727_TruthTable" "" "Test"))) ::
		(Build_TTMetamodel_ELink RowCellsEReference (BuildRowCells  (BuildRow "1832532108_Row" "") ( (BuildCell "423583818_Cell" "" false) ::  (BuildCell "552936351_Cell" "" true) ::  (BuildCell "1471086700_Cell" "" false) ::  (BuildCell "1810742349_Cell" "" true) ::  (BuildCell "154319946_Cell" "" false) :: nil ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "1306834002_Cell" "" true)  (BuildRow "865667596_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "1306834002_Cell" "" true)  (Build_Abstract_Port InputPortEClass  (BuildInputPort "812586739_Port" "" "a") ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "1354083458_Cell" "" false)  (BuildRow "865667596_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "1354083458_Cell" "" false)  (Build_Abstract_Port InputPortEClass  (BuildInputPort "1881901842_Port" "" "b") ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "50699452_Cell" "" true)  (BuildRow "865667596_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "50699452_Cell" "" true)  (Build_Abstract_Port OutputPortEClass  (BuildOutputPort "16868310_Port" "" "s") ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "285133380_Cell" "" true)  (BuildRow "2125062626_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "285133380_Cell" "" true)  (Build_Abstract_Port InputPortEClass  (BuildInputPort "1234250905_Port" "" "d") ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "542365801_Cell" "" false)  (BuildRow "245765246_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "542365801_Cell" "" false)  (Build_Abstract_Port InputPortEClass  (BuildInputPort "1234250905_Port" "" "d") ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "556488341_Cell" "" false)  (BuildRow "13803304_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "556488341_Cell" "" false)  (Build_Abstract_Port OutputPortEClass  (BuildOutputPort "16868310_Port" "" "s") ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "1471086700_Cell" "" false)  (BuildRow "1832532108_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "1471086700_Cell" "" false)  (Build_Abstract_Port InputPortEClass  (BuildInputPort "585324508_Port" "" "c") ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "270095066_Cell" "" true)  (BuildRow "865667596_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "270095066_Cell" "" true)  (Build_Abstract_Port InputPortEClass  (BuildInputPort "585324508_Port" "" "c") ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "929383713_Cell" "" false)  (BuildRow "71706941_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "929383713_Cell" "" false)  (Build_Abstract_Port InputPortEClass  (BuildInputPort "1234250905_Port" "" "d") ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "1270038388_Cell" "" true)  (BuildRow "341138954_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "1270038388_Cell" "" true)  (Build_Abstract_Port InputPortEClass  (BuildInputPort "812586739_Port" "" "a") ))) ::
		(Build_TTMetamodel_ELink RowOwnerEReference (BuildRowOwner  (BuildRow "2125062626_Row" "")  (BuildTruthTable "460201727_TruthTable" "" "Test"))) ::
		(Build_TTMetamodel_ELink RowCellsEReference (BuildRowCells  (BuildRow "2125062626_Row" "") ( (BuildCell "620557167_Cell" "" true) ::  (BuildCell "285133380_Cell" "" true) ::  (BuildCell "1068586139_Cell" "" false) :: nil ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "1292040526_Cell" "" true)  (BuildRow "245765246_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "1292040526_Cell" "" true)  (Build_Abstract_Port InputPortEClass  (BuildInputPort "812586739_Port" "" "a") ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "574268151_Cell" "" true)  (BuildRow "38262958_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "574268151_Cell" "" true)  (Build_Abstract_Port OutputPortEClass  (BuildOutputPort "16868310_Port" "" "s") ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "1217875525_Cell" "" false)  (BuildRow "38262958_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "1217875525_Cell" "" false)  (Build_Abstract_Port InputPortEClass  (BuildInputPort "812586739_Port" "" "a") ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "890545344_Cell" "" true)  (BuildRow "13803304_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "890545344_Cell" "" true)  (Build_Abstract_Port InputPortEClass  (BuildInputPort "585324508_Port" "" "c") ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "1813187653_Cell" "" false)  (BuildRow "38262958_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "1813187653_Cell" "" false)  (Build_Abstract_Port InputPortEClass  (BuildInputPort "585324508_Port" "" "c") ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "510147134_Cell" "" false)  (BuildRow "245765246_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "510147134_Cell" "" false)  (Build_Abstract_Port InputPortEClass  (BuildInputPort "585324508_Port" "" "c") ))) ::
		(Build_TTMetamodel_ELink RowOwnerEReference (BuildRowOwner  (BuildRow "245765246_Row" "")  (BuildTruthTable "460201727_TruthTable" "" "Test"))) ::
		(Build_TTMetamodel_ELink RowCellsEReference (BuildRowCells  (BuildRow "245765246_Row" "") ( (BuildCell "1292040526_Cell" "" true) ::  (BuildCell "726181440_Cell" "" true) ::  (BuildCell "510147134_Cell" "" false) ::  (BuildCell "542365801_Cell" "" false) ::  (BuildCell "2051120548_Cell" "" true) :: nil ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "48208774_Cell" "" false)  (BuildRow "71706941_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "48208774_Cell" "" false)  (Build_Abstract_Port InputPortEClass  (BuildInputPort "585324508_Port" "" "c") ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "1604002113_Cell" "" false)  (BuildRow "769530879_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "1604002113_Cell" "" false)  (Build_Abstract_Port OutputPortEClass  (BuildOutputPort "16868310_Port" "" "s") ))) ::
		(Build_TTMetamodel_ELink RowOwnerEReference (BuildRowOwner  (BuildRow "341138954_Row" "")  (BuildTruthTable "460201727_TruthTable" "" "Test"))) ::
		(Build_TTMetamodel_ELink RowCellsEReference (BuildRowCells  (BuildRow "341138954_Row" "") ( (BuildCell "1270038388_Cell" "" true) ::  (BuildCell "1973233403_Cell" "" true) ::  (BuildCell "63387985_Cell" "" true) ::  (BuildCell "1029472813_Cell" "" false) ::  (BuildCell "1866875501_Cell" "" false) :: nil ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "2051120548_Cell" "" true)  (BuildRow "245765246_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "2051120548_Cell" "" true)  (Build_Abstract_Port OutputPortEClass  (BuildOutputPort "16868310_Port" "" "s") ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "1973233403_Cell" "" true)  (BuildRow "341138954_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "1973233403_Cell" "" true)  (Build_Abstract_Port InputPortEClass  (BuildInputPort "1881901842_Port" "" "b") ))) ::
		(Build_TTMetamodel_ELink RowOwnerEReference (BuildRowOwner  (BuildRow "38262958_Row" "")  (BuildTruthTable "460201727_TruthTable" "" "Test"))) ::
		(Build_TTMetamodel_ELink RowCellsEReference (BuildRowCells  (BuildRow "38262958_Row" "") ( (BuildCell "1217875525_Cell" "" false) ::  (BuildCell "1787079037_Cell" "" true) ::  (BuildCell "1813187653_Cell" "" false) ::  (BuildCell "1353530305_Cell" "" false) ::  (BuildCell "574268151_Cell" "" true) :: nil ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "552936351_Cell" "" true)  (BuildRow "1832532108_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "552936351_Cell" "" true)  (Build_Abstract_Port InputPortEClass  (BuildInputPort "1881901842_Port" "" "b") ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "1427040229_Cell" "" false)  (BuildRow "769530879_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "1427040229_Cell" "" false)  (Build_Abstract_Port InputPortEClass  (BuildInputPort "1881901842_Port" "" "b") ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "1353530305_Cell" "" false)  (BuildRow "38262958_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "1353530305_Cell" "" false)  (Build_Abstract_Port InputPortEClass  (BuildInputPort "1234250905_Port" "" "d") ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "363509958_Cell" "" false)  (BuildRow "71706941_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "363509958_Cell" "" false)  (Build_Abstract_Port OutputPortEClass  (BuildOutputPort "16868310_Port" "" "s") ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "802243390_Cell" "" false)  (BuildRow "13803304_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "802243390_Cell" "" false)  (Build_Abstract_Port InputPortEClass  (BuildInputPort "812586739_Port" "" "a") ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "2033968586_Cell" "" false)  (BuildRow "71706941_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "2033968586_Cell" "" false)  (Build_Abstract_Port InputPortEClass  (BuildInputPort "1881901842_Port" "" "b") ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "1029472813_Cell" "" false)  (BuildRow "341138954_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "1029472813_Cell" "" false)  (Build_Abstract_Port InputPortEClass  (BuildInputPort "1234250905_Port" "" "d") ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "423583818_Cell" "" false)  (BuildRow "1832532108_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "423583818_Cell" "" false)  (Build_Abstract_Port InputPortEClass  (BuildInputPort "812586739_Port" "" "a") ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "154319946_Cell" "" false)  (BuildRow "1832532108_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "154319946_Cell" "" false)  (Build_Abstract_Port OutputPortEClass  (BuildOutputPort "16868310_Port" "" "s") ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "1787079037_Cell" "" true)  (BuildRow "38262958_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "1787079037_Cell" "" true)  (Build_Abstract_Port InputPortEClass  (BuildInputPort "1881901842_Port" "" "b") ))) ::
		(Build_TTMetamodel_ELink RowOwnerEReference (BuildRowOwner  (BuildRow "13803304_Row" "")  (BuildTruthTable "460201727_TruthTable" "" "Test"))) ::
		(Build_TTMetamodel_ELink RowCellsEReference (BuildRowCells  (BuildRow "13803304_Row" "") ( (BuildCell "802243390_Cell" "" false) ::  (BuildCell "702061917_Cell" "" true) ::  (BuildCell "890545344_Cell" "" true) ::  (BuildCell "556488341_Cell" "" false) :: nil ))) ::
		(Build_TTMetamodel_ELink RowOwnerEReference (BuildRowOwner  (BuildRow "71706941_Row" "")  (BuildTruthTable "460201727_TruthTable" "" "Test"))) ::
		(Build_TTMetamodel_ELink RowCellsEReference (BuildRowCells  (BuildRow "71706941_Row" "") ( (BuildCell "1771667101_Cell" "" true) ::  (BuildCell "2033968586_Cell" "" false) ::  (BuildCell "48208774_Cell" "" false) ::  (BuildCell "929383713_Cell" "" false) ::  (BuildCell "363509958_Cell" "" false) :: nil ))) ::
		nil)
	).
