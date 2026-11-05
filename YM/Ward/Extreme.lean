import YM.Ward.Circles

/-!
# Move one slot while it remains strictly extreme, including projection ties.

Can move any one coordinate (including normal). Don't require time-distinct
all points at start. Fits only within entire separated domain. Reflection for
earlier via actual SIGNED label, not Lie spin. These are scalar AnalyticAt.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Ward
open Function Set Filter Complex Analysis Table OS Word
open scoped Topology NNReal ENNReal InnerProductSpace ContDiff BigOperators
variable {G : Gauge} {L : Register G} {S : Table L} {a : Axis}
variable {n : ℕ}

lemma raw (q : Fin n → S.Tag) (x : Points n) : S.read x (fun i => expose (q i))=disc q x := rfl
lemma tags (q : Fin n → L.Token) (H : S.Hierarchy) (x : Points n) (hx : x ∈ conf _) : S.read x q=disc (fun i => S.classTokens (q i)) x :=
    (at_project S S H.laws.toSymmetric (fun _ => le_rfl) hx q).symm

variable (V : Chamber S a)
include V in
/-- upper x changes at coordinate b, manual reflect region because comparison
line Ward uses oriented. `T` rights. -/
lemma higher (H : S.Hierarchy) (W : DiffPlan S) (T : SpinRows S) (P : W.Derivatives S) (Y : Collinear W T) (C : commutes W T) (x : E4)
    (b : Axis) (v : L.Word) (u : S.Tag) (hx : distinct v) (s : ℝ) (h : ∀ p∈v, p.1 a < inc b x s a) :
    AnalyticAt ℝ (fun t => S.expect ((inc b x t,expose u)::v)) s := by
  classical
  have he : ∀ᶠ r : ℝ in 𝓝[<] (inc b x s a), ∀ i ∈ v, i.1 a < r := by
    have hg i (hi : i∈v) : ∀ᶠ r : ℝ in 𝓝[<] (inc b x s a), i.1 a<r :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (Ioi_mem_nhds (h i hi))
    simpa using (eventually_all_finset v.toFinset).mpr (fun i hi => hg i (by simpa using hi))
  obtain ⟨k,hk,hb⟩ := (he.and self_mem_nhdsWithin).exists
  let w := -(k • basis a)
  have hF : Positive (reflect (carry v w) a) a := by
    refine ⟨reflects a (still hx _), fun p hp => ?_⟩
    rw [reflectedPoint,List.mem_map] at hp
    obtain ⟨r,hr,rfl⟩ := hp; rw [List.mem_reverse] at hr
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
    simp [w, Signed.mirrored]; linarith [hk _ hi]
  let i : Future L a := ⟨_,hF⟩
  let y := x+w
  let t (s : ℝ) := inc b y s
  have hh r : t r=inc b x r+w := by unfold t y inc; abel
  have hp : 0 < t s a := by rw [hh]; change k < inc b x s a at hb; simpa [w,inc] using hb
  have hb' r (hr : 0<t r a) : S.expect ((inc b x r,expose u)::v)=inner ℂ (V.GNS.plant i) (spot V u (t r)) := by
    have H_d : distinct ((inc b x r,expose u)::v) := by
      apply locations.mpr
      apply List.nodup_cons.mpr
      refine ⟨?_,locations.mp hx⟩
      rintro hi
      obtain ⟨p,hp,he⟩ := List.mem_map.mp hi
      rw [hh] at hr; simp [w] at hr
      have hv : p.1 a<k := hk _ hp
      rw [he] at hv; simp [inc] at hv; exact hv.not_ge hr.le
    rw [← invariance H.translations H_d w,warm _ _ hr,V.GNS.measure]
    change S.expect ((inc b x r+w,expose u)::carry v w)=S.expect (reflect (reflect (carry v w) a) a ++ [(t r,expose u)])
    rw [OS.reflect_twice,hh]
    exact (Table.order S H.laws.toSymmetric (still H_d w) (@List.perm_append_comm _ [(_,expose u)] (carry v w))).symm
  have hA : AnalyticAt ℝ (fun r => spot V u (t r)) s := by
    by_cases e : b=a
    · subst b; exact advancing V u y s hp
    exact pure V H T W C Y P u y (by simpa [t,inc,Ne.symm e] using hp) e s
  apply (((innerSL ℂ (V.GNS.plant i)).restrictScalars ℝ |>.analyticAt _).comp hA).congr
  have hy : Continuous t := continuous_const.add (continuous_id.smul continuous_const)
  have hw : Continuous (fun i => t i a) := Continuous.comp (f := t) (show Continuous (fun v : E4 => v a) by fun_prop) hy
  filter_upwards [hw.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hp)] with r hr
  exact (hb' _ hr).symm

def Latest (x : Points n) (a : Axis) (k : Fin n) := x∈conf n ∧ ∀ j, j≠k → x j a < x k a
def Earliest (x : Points n) (a : Axis) (k : Fin n) := x∈conf n ∧ ∀ j, j≠k → x k a < x j a

lemma tip {x : Points (n+1)} (r : ℝ) (j : Axis) : cast x 0 j r = Points.cons (inc j (x 0) r) (Points.tail x) := by
  apply PiLp.ext; intro i
  refine Fin.cases ?_ (fun k => ?_) i <;> simp [Points.cons,Points.tail,cast,Points.direction,inc]

include V in
private lemma head_adv (H : S.Hierarchy) (W : DiffPlan S) (T : SpinRows S) (P : W.Derivatives S) (Y : Collinear W T)
    (C : commutes W T) (x : Points (n+1)) (b : Axis) (q : Fin (n+1) → S.Tag) (s : ℝ)
    (h : Latest (cast x 0 b s) a 0) :
    AnalyticAt ℝ (disc q ∘ cast x 0 b) s := by
  let w := Word.realize (fun i : Fin n => expose (q i.succ)) (Points.tail x)
  have hu : distinct w := by
    apply (Word.realized _ _).mpr
    have he := Points.tail_in h.1
    simpa [tip,Points.tail, Points.cons,points] using he
  have hh : ∀ i∈w, i.1 a < inc b (x 0) s a := by
    intro i hi
    obtain ⟨j,hj⟩ := List.mem_ofFn.mp hi; subst i
    simpa [tip,Points.tail,Points.cons] using h.2 j.succ j.succ_ne_zero
  have he u : disc q (cast x 0 b u) = S.expect ((inc b (x 0) u,expose (q 0))::w) := by
    rw [tip,← raw,← S.readAt]; unfold realize
    rw [List.ofFn_succ]
    simp [w, Points.cons, realize]
  rw [Function.comp_def]; rw [funext he]; exact higher V H W T P Y C _ b w (q 0) hu s hh

lemma reordering {x : Points n} (r : Equiv.Perm (Fin n)) (i : Fin n) (b) (u : ℝ) :
    cast (Points.rearrange r x) i b u=Points.rearrange r (cast x (r i) b u) := by
  unfold cast; rw [← Points.arranged r x,← Points.arranged r, map_add,map_smul, Points.directed]

include V in
lemma last_adv (H : S.Hierarchy) (W : DiffPlan S) (T : SpinRows S) (P : W.Derivatives S) (Y : Collinear W T)
    (C : commutes W T) (x : Points n) (j : Fin n) (b : Axis) (q : Fin n → S.Tag) (s : ℝ) (h : Latest (cast x j b s) a j) :
    AnalyticAt ℝ (disc q ∘ cast x j b) s := by
  classical
  cases n with
  | zero => exact Fin.elim0 j
  | succ n =>
    let r := Equiv.swap 0 j
    have hv : r 0=j := Equiv.swap_apply_left _ _
    let U := Points.rearrange r x
    have hh : Latest (cast U 0 b s) a 0 := by
      rw [show cast U 0 b s=_ from reordering _ _ _ _,hv]
      refine ⟨Points.rearrange_in _ h.1,?_⟩
      intro i hi; simp only [Points.rearrange_at, hv]
      exact h.2 (r i) (fun he => hi (r.injective (he.trans hv.symm)))
    apply (head_adv V H W T P Y C U b (q ∘ r) s hh).congr
    filter_upwards [(moves x j b s).continuousAt.preimage_mem_nhds ((conf_open _).mem_nhds h.1)] with i hi
    change disc _ (cast U 0 b i)=disc q _; rw [show cast U _ b i=_ from reordering (x := x) r 0 _ _, hv]
    exact S.class_perm S H.laws.toSymmetric _ hi q

private lemma spiegel (x : Points n) (i : Fin n) (b : Axis) (t : ℝ) :
    Points.move (Signed.reflect a) (cast x i b t)=cast (Points.move (Signed.reflect a) x) i b (if b=a then -t else t) := by
  apply PiLp.ext; intro k; simp only [cast,Points.move_coord,PiLp.add_apply,PiLp.smul_apply]
  rw [show Ortho.move _ (_+_)=_ from (Ortho.motion _).map_add _ _]
  congr 1; by_cases h : k=i
  · subst k; ext j; simp [Signed.mirrored,Points.direction]; split_ifs <;> simp_all
  simp [Points.direction,h, Signed.ortho_move,Signed.reflect]

include V in
lemma first_adv (H : S.Hierarchy) (W : DiffPlan S) (T : SpinRows S) (P : W.Derivatives S) (Y : Collinear W T)
    (C : commutes W T) (x : Points n) (j : Fin n) (b : Axis) (q : Fin n → S.Tag) (s : ℝ) (h : Earliest (cast x j b s) a j) :
    AnalyticAt ℝ (disc q ∘ cast x j b) s := by
  let k := Signed.mirror a
  let Z := Points.move (n := n) (Signed.reflect a)
  let p := L.move k ∘ fun i => expose (q i)
  let F := disc (S.classTokens ∘ p)
  let d (i : ℝ) := if b=a then -i else i
  have hh : Latest (cast (Z x) j b (d s)) a j := by
    rw [show cast _ _ _ _ = Z (cast x j b s) from (spiegel ..).symm]
    exact ⟨Points.move_in _ h.1,fun i hi => by simpa [Z,Signed.mirrored] using h.2 i hi⟩
  have he : AnalyticAt ℝ (F ∘ cast (Z x) j b) (d s) := last_adv V H W T P Y C _ _ _ _ _ hh
  have ht : AnalyticAt ℝ d s := by
    by_cases hx : b=a
    · rw [show d= -id from funext fun i => by simp [d,hx]]; apply analyticAt_id.neg
    rw [show d=id from funext fun i => by simp [d,hx]]; exact analyticAt_id
  apply (he.comp ht).congr
  filter_upwards [(moves x j b s).continuousAt.preimage_mem_nhds ((conf_open _).mem_nhds h.1)] with i hi
  change disc _ (cast (Z x) j b (d i))=disc q _
  rw [show cast _ _ _ _= Z (cast x j b i) from (spiegel ..).symm,
    Function.comp_def,← tags p H _ (show Z (cast x _ b i)∈conf _ from Points.move_in _ (show cast x _ b i∈conf _ from hi)), ← raw]
  exact H.spin.mirror k hi _
end YM.Ward
