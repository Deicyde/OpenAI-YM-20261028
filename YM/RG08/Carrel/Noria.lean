import YM.RG08.Anchor.Curls
import YM.RG08.Camera.Due

/-!
# Relative stencil cards → network vertices on cover. Hold any leg after rooting, costs
pre-analytic diameter Held, no type-cardinality loss repeated along legs. Exact pour on tori.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Carrel
open Lattice Laurent Forms Pert.Bulk Isles Packets Glyph Filter Finset Function
open scoped BigOperators Topology Classical ENNReal
variable {I:Type}{n:ℕ}
abbrev Slide (I:Type)(n:ℕ):=Tape n (Market I)

def shelf (x:Slide I n):ℝ:=max 0 ((carpet I).radius x) -- diameter, not absolute! fine
lemma shelf_diam (x:Slide I n):shelf x=(carpet I).radius x:= max_eq_right (Ground.radius_nn ..)
lemma shelf_sway (q:Cover)(x:Slide I n):shelf (sway q x)=shelf x:=by
 simp only [shelf_diam];apply Ground.radius_map;intro u v
 simp only [carpet,pass,sep,add_sub_add_right_eq_sub]

-- Ledger may assign every translated copy, so sum *before* identifying; retain U.
abbrev Cost (x:Flake n (Market I))(σ:ℝ):= ∑' z,bill (x z) (σ*shelf z)
def Won (F:Flake n (Market I))(σ p:ℝ):Prop := 0≤p ∧ Cost F σ≤ENNReal.ofReal p
variable {F G:Flake n (Market I)}{σ p:ℝ}
private lemma bore (h:Won F σ p): Summable fun v=> |F v| *Real.exp (σ*shelf v):= Pert.Bulk.bill_ne_top (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h.2) -- name?
lemma word_abs (h:Won F σ p)(hh:0≤σ): Summable fun v=> |F v|:=
 (bore h).of_nonneg_of_le (fun _=>abs_nonneg _) (fun u=>le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp (mul_nonneg hh (show 0≤shelf u by unfold shelf; exact le_max_left ..))))
lemma word_sum (h:Won F σ p)(hh:0≤σ):Summable F:=(word_abs h hh).of_abs

/-- Physical coefficient obtained by summing over translation center. at n=0 total on
cover meaningless; not asserted. -/
def grown (F:Flake n (Market I)):Flake n (Market I):=fun x=>∑' q:Cover,F (sway (-q) x)
lemma grown_y (F:Flake n (Market I)):Cohort (grown F):=by
 intro q x;unfold grown;rw [←(Equiv.addRight q).tsum_eq];apply tsum_congr;intro y;simp [sway_sway]

lemma ankle {a:Market I}{i:Fin n}:Injective (fun t:Cover×{w:Slide I n| w i=a}=>sway (-t.1) (t.2.val)):=by
 rintro ⟨b,⟨u,hu⟩⟩ ⟨c,⟨v,hv⟩⟩ hh
 have he:=congrArg Prod.fst (congrFun hh i)
 change (u i).1 + -b=(v i).1+-c at he
 rw [show u i=a from hu,show v i=a from hv] at he
 obtain rfl : b=c:=neg_inj.mp (add_left_cancel he)
 have hz:u=v:=(tides (-b)).injective hh
 subst hz;rfl
lemma grown_held (h:Won F σ p): Held (carpet I) σ p (grown F):=by
 rw [ensign]
 intro i a
 let V:=fun x:Slide I n=>bill (F x) (σ*shelf x)
 let U:=fun x:Slide I n=>bill (grown F x) (σ*(carpet I).radius x)
 have he :∑' x,Forms.row (mark (carpet I) σ (grown F)) i a x=∑' x:{x:Slide I n// x i=a}, U x.val:=by
    let S:Set (Slide I n):={x|x i=a};change _=∑' x:S,U x.val;rw [_root_.tsum_subtype]
    apply tsum_congr;intro z
    unfold Forms.row Set.indicator mark; by_cases hv:z i=a <;> simp [S,hv,U]
 rw [he]
 calc
 _ ≤ ∑' x:{x:Slide I n//x i=a},∑' q:Cover,V (sway (-q) x.val):=ENNReal.tsum_le_tsum fun z=>by
    unfold U grown
    apply (bill_tsum _ _).trans
    apply ENNReal.tsum_le_tsum;intro q; unfold V;rw [shelf_sway,shelf_diam]
 _ ≤ _:=by
    have hh: ∑' t:Cover×{x:Slide I n//x i=a},V (sway (-t.1) t.2.1)≤∑' x,V x:=ENNReal.tsum_comp_le_tsum_of_injective ankle V
    rw [ENNReal.tsum_prod',ENNReal.tsum_comm] at hh;exact hh.trans h.2

end YM.RG08.Carrel
