import YM.RG08.Atrium.Pass
import YM.RG08.Forms.PontChange
/-!
# Single-Mark Wisp charge through seam. DK on Neck. Parade upgrade to width meet
 after tested transport and re-root. Use weight around fine REPRESENTATIONAL
 foot, not cell frump. Named Ground fee F.In.W. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Necks
open Forms Function Finset Jetty Lattice Isles Pert.Bulk Stationary Spar Camera Glyph Filter Laurent RG Precision Exterior Skiff Trickle Weald Hatch Carrel Quarry
open Planned.PrimaryIntegral295 Place Carrier Flint Lagoon Yurt Next.Free
open scoped Classical ContDiff BigOperators Topology ENNReal
variable {I J:Type}{n m d p:ℕ}{σ τ μ V Q B C δ η:ℝ}{L:Jetty.Loom I}{D:Jetty.Loom J}
variable {h:0<σ}{F F':Pack n I}

def services (u:Pearl→Pearl)(a:I→J)(P:Pack n I):Pack n J:=broom a (fun i p=>P i (u p))
-- generalizes toolish; σ_out can exceed σ_in as dilation on tests and on height permits.
lemma aboard (u:Pearl→Pearl)(a:I→J)(he:Lyrics F)(hs:Sings L d h F V)(_hV:0≤V)(ht:0<τ)(hu:∀ x,Jetty.beam d ht x≤1 → Jetty.beam d h (u x) ≤ Q)
 (hx:∀ i,τ* D.height (a i)≤σ*L.height i+B)(hB:0≤B)(hQ:0≤Q):Sings D d ht (services u a F) (Real.exp B*Q*V):=by
 let v(y:Tape n J)(x:Tape n I)(b:Pearl):ℝ:=if y=a∘x then F x (u b) else 0
 let q:ℝ:=Real.exp B*Q; have hq:0 ≤ q:= mul_nonneg (Real.exp_pos _).le hQ
 let E:ℝ≥0∞:=ENNReal.ofReal q
 have hA(y x):gems D d ht (fun _ :Tape n J=>v y x) y ≤ if y=a∘x then E*gems L d h F x else 0:=by
    unfold gems; split_ifs with hi
    · subst y; unfold v; simp only [ite_true]; have hw:=Skiff.shares (he x) (d:=d) (W:=u) hu
      have Hz:τ *D.cage (a ∘ x) ≤ σ*L.cage x+B:=by
         rw [mul_comm τ,←le_div_iff₀ ht];apply D.racks _ (div_nonneg (add_nonneg (mul_nonneg h.le (L.cage_nn _)) hB) ht.le)
         intro i;rw [le_div_iff₀ ht,mul_comm];exact (hx (x i)).trans (add_le_add_left (mul_le_mul_of_nonneg_left (L.float x i) h.le) B)
      apply (mul_le_mul' hw (show weft D τ (a∘x) ≤ ENNReal.ofReal (Real.exp B)*weft L σ x from ?_)).trans_eq;swap
      · unfold weft;rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,←Real.exp_add]; exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (Hz.trans_eq (add_comm ..)))
      unfold E q;rw [ENNReal.ofReal_mul (Real.exp_pos _).le];ac_rfl
    unfold v; simp_rw [if_neg hi]; exact le_of_eq (by rw [show (fun _:Pearl=>(0:ℝ))=(0:NoteX) from rfl,purse_zero,zero_mul] ) -- change notation
 calc
  _ ≤ ∑' y:Tape n J, ∑' x:Tape n I,if y=a∘x then E*gems L d h F x else 0:= ENNReal.tsum_le_tsum (fun y=>?_)
  _ ≤ _:=by rw [ENNReal.tsum_comm];simp_rw [tsum_ite_eq, ENNReal.tsum_mul_left];apply (mul_le_mul_right hs _).trans;unfold E q;rw [ENNReal.ofReal_mul hq] -- hq uses q
 unfold gems services broom
 change Jetty.purse d ht (fun p=>∑' i,v y i p) * _≤ _
 apply (mul_le_mul_left (Jetty.purse_sum _ _ (v y)) _).trans
 rw [←ENNReal.tsum_mul_right];apply ENNReal.tsum_le_tsum
 exact fun i=>hA y i

variable {G:Gauge}
local notation "A"=> Loc G 1
local notation "E"=>Market A
-- exact counterpart over faithful Embassy. Salary uniform over L (even if τ larger than σ_in).
def steeped (P:Patch)(o:Site P.L)(S:Pack n E):Pack n (Market (Tack.Head P G)):=services (aisle (dip P.L) (ahead P.L o)) (Hatch.door P o) S
lemma steeped_apply(P:Patch)(o:Site P.L)(S:GrainS E)(e:ℕ):plank P o (flow P.L o S) e n=steeped P o (S e n):=rfl
lemma ferryA (P:Patch)(o:Site P.L){S:Pack n E}(he:Lyrics S)(hs:Sings (stance A) d h S C)(hC:0≤C)(hk:0<τ)(hτ:τ≤1)(hp:τ*unitStep P.L≤σ) : Sings (stance _) d hk (steeped P o S) (Real.exp 16*C):=by
 rw [show (16:ℝ)=12+4 from by norm_num,Real.exp_add]
 unfold steeped;apply aboard _ _ he hs hC hk ?_ ?_ (by norm_num) (Real.exp_pos _).le
 · intro f hf; refine (spending (d:=d) (h:=h) hk (ahead P.L o) (unitStep P.L) (by rw [abs_of_pos (unitStep_pos _)]; exact unitStep_le _) (by rwa [abs_of_pos (unitStep_pos _)]) f).trans ?_
   apply (mul_le_of_le_one_left (Real.exp_pos _).le hf).trans (Real.exp_le_exp.mpr ?_); exact (mul_le_mul hτ (heading ..) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
 intro i;let a:=abroad i;have hv:0≤a:=abroad_nn _
 change τ*abroad _≤σ*a+12
 apply (mul_le_mul_of_nonneg_left (height_door ..) hk.le).trans
 change τ*(a/(P.L.val:ℝ)+12)≤_;rw [div_eq_mul_inv, mul_add,mul_left_comm τ a]
 exact add_le_add (le_trans (mul_le_mul_of_nonneg_left hp hv) (le_of_eq (mul_comm a σ))) (by linarith)

lemma ferry_diff (P:Patch)(o:Site P.L){S T:Pack n E}:steeped P o (S-T)=steeped P o S-steeped P o T:=by
 ext y f;unfold steeped services
 by_cases h:∃ i, y=door P o ∘ i
 · obtain ⟨i,h⟩:=h;subst y
   have hp : Injective (fun x:Tape n E=>Hatch.door P o ∘ x):=fun _ _ h=>funext fun j=> step_door P o (congrFun h j)
   unfold broom;simp only [Pi.sub_apply, hp.eq_iff, tsum_ite_eq']; -- rewriting eq_iff door comp i
 unfold broom at *;push Not at h;simp only [Pi.sub_apply]; simp_rw [if_neg (h _)]; simp
lemma steeped_vox (P:Patch)(o:Site P.L){S:Pack n E}(he:Lyrics S)(hs:Sings (stance A) d h S C)(hk:0<τ)(hτ:τ ≤σ):Lyrics (steeped P o S):=by
 have hv:=tilts P.L o S he
 have hh:=sales P.L o S he hs hk hτ
 exact Hatch.cull _ hv hh
lemma ferryPhase (P:Patch)(o:Site P.L){S S':Pack n E}(hf:Dyad (stance A) d h C δ S S')(hk:0<τ)(hτ:τ≤1)(hp:τ*unitStep P.L≤σ):Dyad (stance (Tack.Head P G)) d hk (Real.exp 16*C) δ (steeped P o S) (steeped P o S'):=by
 obtain ⟨hC,hδ,⟨hu,hv⟩,hs,ht,h₁⟩:=hf; constructor
 · exact mul_nonneg (Real.exp_pos _).le hC
 · exact hδ
 · exact ⟨steeped_vox _ _ hu hs h le_rfl,steeped_vox _ _ hv ht h le_rfl⟩
 · apply ferryA P o <;> assumption
 · apply ferryA P o <;> assumption
 rw [←ferry_diff, mul_assoc]; exact ferryA P o (hu.sub hv) h₁ (mul_nonneg hC hδ) hk hτ hp
end YM.RG08.Necks
