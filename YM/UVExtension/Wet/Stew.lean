import YM.UVExtension.Wet.Brook
import YM.UVExtension.Wren.Taxis
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Wet
open Function Filter Finset Lattice Wilson MeasureTheory RG Push Push.AbsoluteSums
open Steady Wren Extra.Histories
open scoped BigOperators Topology ContDiff Classical
variable {G:Gauge}{n:Side}{κ ι α :Type}{v: Filter ι}{t:ℝ}
open PhysicalNext.Repeat Ovens Pipes Mallow Progress.DirectedRecipe Rack
variable (P:BudgetPoint)(X:Pipes G n)(E:ℕ≃ X.Pellet)(d:ι→ Ovens.Tap G n)(W:ι→ℝ→ Code G n)
variable (h:Canted v 0 (fun i j x z=> W i z j x))(hp: Transit v (fun i => (d i).logarithm))
include h hp
lemma freezes : Canted v 0 (fun i j x z=>solid E P (spice (d i) (W i z)) j x):=by
   let f i j x z:= reach (spice (d i) (W i z)) j x; have he:Canted v 0 f:=by
       let q i(j:ℕ) x:= Real.exp ((d i).logarithm j x)-1; have hv :Transit v q:= Gold.pops hp
       let S i (j:ℕ) x z:=W i z j x
       have h': f = fun n i=> Sum.elim (S n) (fun j x _=> q n j x) i := funext fun n=> funext fun i=> by cases i <;> rfl
       rw [h']; exact h.join (Canted.ever _ hv)
   have hv:= he.goods.lenses (fun i=> (E i).val) (Subtype.val_injective.comp E.injective)
   exact hv.lite (fun i x=> (addr E P i).eligible P.threshold x) -- branching instance?
variable [NeBot v]
lemma sparkle : Canted v 0 (fun i j x z=> Mallow.final.frigid X (d i) (W i) P z j x):=by
   let f n t:= W n t; let T n:= Rack.widen X (d n); let w n (t:ℝ):= stuff (Rack.upK X) (f n t)
   have hg i j x z: final.frigid X (d i) (W i) P z j x=solid (folio G n) P (spice (T i) (w i z)) j x:=rfl
   have hv:Canted v 0 (fun n j x z=> w n z j x):=by
       let y:=Rack.upK X
       have hx i n j t:w i t (y n) j=W i t n j:= congr_fun (stuffed ..) j
       have ht i n (h:n∉ Set.range y) x t:w i t n x=0:=congr_fun (blank _ _ h) x
       refine ⟨fun i j x=>?_, (Crumble.streak h.well y).fade ?_,(Crumble.streak h.joys y).fade ?_⟩
       · by_cases he:j∈Set.range y; obtain ⟨k,rfl⟩:=he; simp_rw [hx]; exact h.firms ..
         simp_rw [ht i j he]; exact differentiableAt_const _
       all_goals filter_upwards with i j; funext x; by_cases he:j∈ Set.range y; obtain ⟨j,rfl⟩:=he; simp_rw [stuffed,hx]; try rfl
       rw [blank _ _ he]; simp_rw [ht i j he]; simp
   simp_rw [hg]; apply freezes P (drawer G n) (folio G n) T w hv; exact Crumble.streak hp _
end YM.UVExtension.Wet
