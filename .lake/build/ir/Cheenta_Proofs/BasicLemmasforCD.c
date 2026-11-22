// Lean compiler output
// Module: Cheenta_Proofs.BasicLemmasforCD
// Imports: public import Init public import Mathlib.Data.Fintype.Card public import Mathlib.Data.Real.Basic public import Mathlib.Topology.Basic public import Mathlib.Topology.Compactness.Paracompact public import Mathlib.Topology.Connected.Clopen public import Mathlib.Topology.Order.IntermediateValue public import Mathlib.Topology.Sets.OpenCover
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Fintype_Card(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Real_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Topology_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Topology_Compactness_Paracompact(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Topology_Connected_Clopen(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Topology_Order_IntermediateValue(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Topology_Sets_OpenCover(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_glimpseOfLean_Cheenta__Proofs_BasicLemmasforCD(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Fintype_Card(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Real_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Topology_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Topology_Compactness_Paracompact(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Topology_Connected_Clopen(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Topology_Order_IntermediateValue(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Topology_Sets_OpenCover(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
