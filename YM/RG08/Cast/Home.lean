import YM.RG08.Cast.Pi

/-!
# Native real potential kernel of an arbitrary floor metric
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Cast
open Lattice Laurent Forms Pert.Bulk Isles Packets Carrel Filter Finset Function RG
open Anchor Rudder Rudder.Symmetry Exterior Stationary Bloch RG08.Flat Spar Next.Free Rows
open scoped Topology ContDiff Classical BigOperators ENNReal Matrix
variable {G:Gauge}{I:Type}{r:ℕ}{σ C:ℝ}{P:Side}
variable {B:Precision.Bed}{c : Clip}{D η : ℝ}
local notation "o" => (0:Fin 2)
local notation "u" => (Fin.succ (0:Fin 1))

lemma light_cities (B:Precision.Bed):city 1 (Flat.output B):=by
 unfold Flat.output Flat.writ; rw [← one_mul (1:Side)]; apply pass_bind
 · intro x y v
   simp [swap,Packets.pass,plain,add_sub_add_right_eq_sub]
 rw [← one_mul (1:Side)] ; apply pass_bind _ (pass_one _)
 exact pass_one _

lemma podium (G:Gauge)(h:B.metric.strip σ C)(_hf:∀ P,Precision.Floor B c P η D)(hC:0≤C)(hs:0<σ)(hi:σ≤1):
  -- literal K potential equality, all covers. retain both equations on tori
    beam (n:=1) G (Flat.output B)=picture G.ColorIndex 2 (beam G (plain B.metric)):=by
 let R:=plain B.metric;let U:=Flat.output B
 have hw:= (plain0 h (le_refl _)).1;have hx:= pass_one B.metric
 have hR:=spur_cost (G:=G) hw (from_row R hx hw) hC hs.le
 have hG:=Anchor.expand_path (spur_path hx (G:=G)); have ht:=Anchor.expand_cost hR
 obtain ⟨hb,hb'⟩:=output_cost h hC hs.le hi
 have hh:=spur_cost (G:=G) hb (from_row U (light_cities B) hb) (mul_nonneg Flat.sumToken_pos (by exact mul_nonneg (Nat.cast_nonneg _) hC)) hs.le
 have hk:0≤tax G 2*C:=by unfold tax; positivity
 have he:=Spar.encode (n:=2) (by norm_num) hs hk hG ht
 apply compress_inj (k:=1) _ _ expand_grade (bearing (F:=beam G R) expand_grade).2
 change compress 1 (beam G U)=compress 1 (picture _ _ (beam G R))
 rw [show compress 1 (beam G U)=spur G U from funext (fun x=>extend_top (k:=1) (spur G U) x)]
 apply peepers hh (Anchor.compress_cost _ he) hs (by positivity) o (N:=chain) ?_ (fun i=>?_)
 · rw [tendsto_atTop_atTop];intro b; exact ⟨b,fun i hi=>by change b ≤ (chain i).val; dsimp [chain]; omega⟩
 rw [spur_matches (hb' (chain i))];exact (picture_arcade (matches_plain _) (NextTo.unit hs hk hG ht (by decide))).symm

lemma magnitude_duct {a b:Finset Axis} (ha:a.card=2)(hb:b.card=2) (y:Tape 2 G.ColorIndex)(v:Cover) :Loop.col (hum (beam G (plain B.metric)) y) a b v=
    if y o=y u then B.metric ⟨a,ha⟩ ⟨b,hb⟩ v else 0:=by
 change Anchor.extend 2 (spur G (plain B.metric)) _=_
 unfold Anchor.extend
 let X:=lyre (Loop.place (0,a) (v,b)) y
 rw [dif_pos (show permitted Cover G.ColorIndex 2 X from ?_)]
 · change (if _ then B.metric _ _ (v-0) else 0)=_
   rw [sub_zero]
   rfl
 intro i; fin_cases i;exact ha;exact hb

lemma beam_core (G:Gauge)(B:Precision.Bed)(hf:Precision.Floor B c P η D): Loop.Core (beam G (plain B.metric)) 1:=by
 intro a b ha hb y
 unfold Loop.spectrum Loop.load
 simp_rw [magnitude_duct ha hb];unfold Loop.AxisK;by_cases h:y o=y u
 · simp only [h,if_true,and_true]
   change roadSum _ _ _ = _ -- 1/0 ℝ
   let x:TypeFace 2:=⟨a,ha⟩;let z:TypeFace 2:=⟨b,hb⟩
   have he:=roadSum_price B.metric x z;rw [hf.starts,Matrix.one_apply] at he
   apply Complex.ofReal_injective
   change (Complex.ofReal (roadSum B.metric x z))=_; rw [he];dsimp only [x,z];split_ifs with hv hk hk
   · simp
   · exact (hk (congr_arg Subtype.val hv)).elim
   · exact (hv (Subtype.ext hk)).elim
   simp
 simp only [h,and_false,↓reduceIte];simp
end YM.RG08.Cast
