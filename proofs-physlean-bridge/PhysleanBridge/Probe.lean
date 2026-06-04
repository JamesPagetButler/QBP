import QuantumInfo.Measurements.POVM
import QuantumInfo.States.Mixed.MState
import QuantumInfo.States.Pure.Braket
import QuantumInfo.States.Pure.Qubit

/-! Import-only probe to confirm the PhysLean QuantumInfo measurement/state API
    is importable on the bridge toolchain (AC-T1). -/

#check @POVM
#check @POVM.measure
#check @MState.pure
#check @Ket
