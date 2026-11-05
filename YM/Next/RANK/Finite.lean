import YM.Analysis.Polydisc
import YM.Cells.Corrected
import YM.Cells.Embedded
import YM.Next.RANK.Value
import YM.Pressure.Seeds


/-!
# Fixed-slot corrected estimates and unsubtracted comparison

Any nonempty subset of I must pay; arity and family are fixed, not number of
replicas. The normalizer here uses the freeTable **at specified rescaled
locations**, via its actual Wick moments. Slot operations also at arity zero when appropriate. No estimate on the *phase* assumed or used.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Read
open Function Set Filter RG Lattice Wilson Cells Marker Glyph Exponential MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff ENNReal

variable {G : Gauge} {L : Register G} {n m : ℕ}
variable (S : Table L)

/-- One way of enumerating a subword. -/
def project (T : modes (Fin n)) := (T.val.orderIsoOfFin rfl).toEquiv

def portion (T : modes (Fin n)) (x : Points n) := points fun i => x (project T i).val
lemma portion_free (T : modes (Fin n)) (x : Points n) (h : x∈conf n) : portion T x ∈ conf _ :=
  (show Injective x.ofLp from h).comp (Subtype.val_injective.comp (project T).injective)

lemma portion_cont (T : modes (Fin n)) : Continuous (portion T) := by unfold portion points; fun_prop

def profile (t : Fin n → S.Tag) (x : Points n) : veil (Fin n) := Poly.inject fun T =>
    S.useAt S (portion T x) fun i => t (project T i).val

lemma profile_part (t : Fin n → S.Tag) (x : Points n) (T) : (profile S t x).part T =
    S.useAt S (portion T x) fun i => t (project T i).val := rfl

lemma profile_part_cont (h : S.Smooth) (t : Fin n→S.Tag) (T : modes (Fin n)) :
    ContinuousOn (fun x => (profile S t x).part T) (conf n) :=
  (S.class_smooth S h _).continuousOn.comp (portion_cont T).continuousOn (fun x hx => portion_free T x hx)

theorem profile_tends {X : Type*} {l : Filter X} {f : X → Points n} (t : Fin n→S.Tag)
    (h : S.Smooth) {x} (hc : x∈conf n) (hf : Tendsto f l (𝓝 x)) : Tendsto (fun i => profile S t (f i)) l (𝓝 (profile S t x)) := by
  apply tendsto_pi_nhds.mpr; intro i
  exact (((profile_part_cont S h t i x hc).continuousAt ((conf_open _).mem_nhds hc)).tendsto).comp hf

lemma chart_rec (h : S.Symmetric) (x : Points n) (hx : x∈conf n) (t : Fin n → S.Tag) (T : modes (Fin n))
    (q : Fin m ≃ ↥T.val) : (profile S t x).part T = S.useAt S (points fun i => x (q i).val) (fun i => t (q i).val) := by
  have he : m=T.val.card := by simpa using! Fintype.card_congr q
  subst m
  symm; let e := q.trans (project T).symm
  have hh (i : Fin T.val.card) : (q i).val=(project T (e i)).val := by unfold e; simp
  rw [profile_part]
  simp_rw [hh]; exact S.class_perm S h e (portion_free T x hx) (fun i => t (project T i).val)

lemma profile_vac (h : S.Basic) (x : Points n) (hx : x∈conf n) (t : Fin n → S.Tag) :
    (profile S t x).part (quiet _)=1 := by
  let v : modes (Fin n) := Glyph.quiet (Fin n)
  have hv : v.val.card=0 := rfl
  rw [chart_rec S h.toSymmetric x hx t v ((finCongr hv).symm.trans (project v))]
  have he (w : Fin 0 → S.Tag) (y : Points 0) : S.useAt S y w=1 := h.trivial (fun i => ⟨(w i).1,S.representative _ (w i).2⟩) y
  exact he _ _

lemma profile_full (h : S.Symmetric) (x : Points n) (hx : x∈conf n) (t : Fin n → S.Tag) :
    (profile S t x).part (scene Finset.univ)=S.useAt S x t := by
  let e : Fin n ≃ ↥(scene (Finset.univ (α:=Fin n))).val :=
    { toFun := fun i => ⟨i,Finset.mem_univ i⟩, invFun := Subtype.val, left_inv := fun _ => rfl, right_inv := fun i => rfl }
  exact chart_rec S h x hx t _ e

lemma profile_single (h : S.Symmetric) (x : Points n) (hx : x∈conf n) (t : Fin n → S.Tag) (i : Fin n) :
    (profile S t x).part (scene {i})=S.useAt S (points (fun _ : Fin 1 => x i)) (fun _ => t i) := by
  let e : Fin 1 ≃ ↥(scene {i}).val :=
    { toFun := fun _ => ⟨i, Finset.mem_singleton.mpr rfl⟩
      invFun := fun _ => 0
      left_inv := fun i => Subsingleton.elim ..
      right_inv := fun i => Subtype.ext (Finset.mem_singleton.mp i.property).symm }
  exact chart_rec S h x hx t _ e

lemma profile_pair (h : S.Symmetric) (x : Points n) (hx : x∈conf n) (t : Fin n → S.Tag) (i j : Fin n) (he : i≠j) :
    (profile S t x).part (scene {i,j})= S.useAt S (points ![x i,x j]) ![t i,t j] := by
  let f : Fin 2 → ↥(scene {i,j}).val := ![⟨i,by simp [scene]⟩,⟨j,by simp [scene]⟩]
  have ho : Bijective f := by
    refine ⟨?_, fun a => ?_⟩
    · intro a b h; fin_cases a <;> fin_cases b <;> simp_all [f,he.symm]
    rcases show a.val=i ∨ a.val=j from (by exact (Finset.mem_insert.mp a.property).imp_right Finset.mem_singleton.mp) with hv|hv
    · exact ⟨0,Subtype.ext (by simp [f,hv])⟩
    · exact ⟨1,Subtype.ext (by simp [f,hv])⟩
  rw [chart_rec S h x hx t (scene {i,j}) (Equiv.ofBijective f ho)]
  congr 1
  · apply PiLp.ext; intro p; fin_cases p <;> rfl
  funext p; fin_cases p <;> rfl

variable {X V : Type*} [Fintype V] [DecidableEq V]

def bareP (a : V → X → ℂ) : X → veil V := fun x => raw fun i => a i x

def cylinder (D : veil V) (a : V → X → ℂ) (x : X) := Poly.pass (-D)*bareP a x

@[simp] lemma parts_vac (a : V → X → ℂ) (x : X) : (bareP a x).part (quiet _)=1 := by unfold bareP; simp
lemma parts_word (a : V → X → ℂ) (x : X) (T : modes V) : (bareP a x).part T=∏ i∈T.val,a i x := expand ..

lemma raw_cont [TopologicalSpace X] (a : V → X → ℂ) (h : ∀ i,Continuous (a i)) (T) :
    Continuous fun U => (bareP a U).part T := by
  simp_rw [parts_word]; exact continuous_finsetProd _ (fun i _ => h i)

lemma cylinder_cont [TopologicalSpace X] (a : V → X → ℂ) (h : ∀ i,Continuous (a i)) (T) (D) :
    Continuous fun x => (cylinder D a x).part T := by
  simp_rw [cylinder,Glyph.part_mul]; exact continuous_finsetSum _ fun i _ => continuous_const.mul (raw_cont a h _)

section
variable {D F : veil V} (h : Expands D F) (P : V → X → ℂ)
include h

lemma unit_price (x) : (cylinder D P x).part (quiet _)=1 := by
  have he : (-D).part (Glyph.quiet _) = 0 := by simp only [Poly.part_neg,h.1,neg_zero]
  rw [cylinder, Poly.quiet_mul,Poly.pass_part _ he,parts_vac,one_mul]

lemma retrieve (T : modes V) (x : X) :
    (∏ i∈T.val,P i x) = F.part T +
      ∑ s ∈ (T.val.powerset.erase T.val), F.part (scene s) * (cylinder D P x).part (scene (T.val\s)) := by
  have he : F * cylinder D P x = bareP P x := correct h _
  rw [← parts_word,← he,Glyph.part_mul,← Finset.add_sum_erase _ _ (show T.val∈T.val.powerset by simp)]
  congr 1; rw [Finset.sdiff_self,scene_nil,unit_price h, scene_of, mul_one]

lemma cylinder_single (u : V) (x : X) :
    (cylinder D P x).part (slot u)=P u x-F.part (slot u) := by
  have hv : F.part (quiet V)=1 := h.2 ▸ Poly.pass_part _ h.1
  have he := retrieve h P (scene {u}) x
  change (∏ i∈{u},P i x)= F.part (slot u) + (∑ s∈Finset.erase (Finset.powerset {u}) {u}, F.part (scene s)*(cylinder D P x).part (scene ({u} \ s))) at he
  have hh : (Finset.powerset {u}).erase {u}={∅} := by
    calc
      _ = ((insert u (∅:Finset V)).powerset.erase {u}) := by simp
      _ = _ := by rw [Finset.powerset_insert]; simp; ext q; by_cases q = ∅ <;> simp [*]
  rw [hh,Finset.prod_singleton,Finset.sum_singleton,Finset.sdiff_empty,scene_nil,scene_single,hv,one_mul] at he
  rw [he]; abel

lemma cylinder_pair (u v : V) (hu : u≠v) (x : X) :
    (cylinder D P x).part (scene {u,v})=(P u x-F.part (slot u))*(P v x-F.part (slot v))-
      (F.part (scene {u,v})-F.part (slot u)*F.part (slot v)) := by
  have hv : F.part (quiet V)=1 := h.2 ▸ Poly.pass_part _ h.1
  have he := retrieve h P (scene {u,v}) x
  let S : Finset V := {u,v}
  change (∏ i∈S,P i x)= F.part (scene S) +
    (∑ s∈Finset.erase S.powerset S, F.part (scene s)*(cylinder D P x).part (scene (S \ s))) at he
  have hc : S.powerset.erase S={∅,{u},{v}} := by
    change Finset.erase ((insert u (insert v (∅:Finset V))).powerset) S=_
    have hx (a : Finset V) (hh : a.card<2) : a≠{u,v} := fun H => by rw [H,Finset.card_pair hu] at hh; omega
    have H := hx ∅ (by simp)
    have H' := hx {u} (by simp)
    have H'' := hx {v} (by simp)
    rw [Finset.powerset_insert,Finset.powerset_insert]; simp [S]; ext
    simp only [Finset.mem_erase,Finset.mem_insert,Finset.mem_singleton]; grind
  have hu' : {u}≠({v} : Finset V) := by simp [hu]
  have hp : S \ {u}={v} := by ext w; by_cases i : w=u <;> simp [S,i,hu]
  have hq : S \ {v}={u} := by ext; simp [S,hu]
  rw [hc,Finset.sum_insert (by simp),Finset.sum_pair hu',hp,hq,Finset.sdiff_empty, scene_nil,hv,one_mul,
    scene_single,scene_single,cylinder_single h,cylinder_single h, show (∏ i ∈ S,P i x)=P u x*P v x from Finset.prod_pair hu] at he
  change (cylinder D P x).part (scene S)= _ - (_ - _)
  linear_combination -he
end

section cell
variable {r : Side} (T : Tiling r) (P : V → Config G r → ℂ) (η : ℝ)
  {β : ℝ} (w : Seam G r β)

private lemma piles {ι : Type*} (s : Finset ι) (F : ι → Config G r → ℂ) (hx : ∀ i∈s, Interior (T.chamber 0) (F i)) :
    Interior (T.chamber 0) (fun U => ∑ i∈s,F i U) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact Interior.constant _ _
  | @insert i t hi ih =>
    simp_rw [Finset.sum_insert hi]; exact (hx i (Finset.mem_insert_self ..)).plus (ih (fun k hk => hx k (by simp [hk])))

lemma raw_in (hp : ∀ i, Interior (T.chamber 0) (P i)) (D : veil V) (s) :
    Interior (T.chamber 0) (fun U => (cylinder D P U).part s) := by
  simp_rw [cylinder,Glyph.part_mul,parts_word]
  apply piles T; exact fun i _ => (Interior.combines _ _ (fun i _ => hp i)).scale _

include w
private lemma gets (z : Config G r→ ℂ) (hz : Interior (T.chamber 0) z) : ‖moment β z‖ ≤ T.rootTest β z := by
  have h := T.planted w (fun _ : Fin 1 => 0) (fun i j _ => Subsingleton.elim i j) (fun _ => z) (fun _ => hz)
  simpa [Fin.prod_univ_succ] using h

/-- Each subset, not just the entire occupied-cell moment. Cost of multiplying back
free moments is a finite-family cost. -/
theorem maxwell {D F : veil V} (h : Expands D F) (hp : ∀ i, Interior (T.chamber 0) (P i))
    (he : 0≤η) (ht : ∀ s : modes V,s.val.Nonempty → T.rootTest β (fun U => (cylinder D P U).part s) ≤ η) (s : modes V) :
    ‖moment β (fun U => ∏ i∈s.val,P i U) - F.part s‖ ≤ Poly.price (fun _ => 1) F * η := by
  let b (t : modes V) := fun U => (cylinder D P U).part t
  have hi (y : modes V) : Integrable (b y) (law G r β) := (raw_in T P hp D y).integrable β
  let S := s.val.powerset.erase s.val
  let c (i : Finset V) := F.part (scene i) * moment β (b (scene (s.val \ i)))
  have hv : moment β (fun U => ∏ i∈s.val,P i U) - F.part s = ∑ i∈ S,c i := by
    simp_rw [retrieve h P]
    unfold moment
    let Q (i : Finset V) := fun U => F.part (scene i)*b (scene (s.val \ i)) U
    change (∫ U, F.part s+∑ i∈S,Q i U∂law G r β)-_=_
    have hu i : Integrable (Q i) (law G r β) := (hi _).const_mul _
    rw [integral_add (integrable_const _) (integrable_finsetSum _ fun i _ => hu i), integral_finsetSum _ (fun i _ => hu i)]
    simp only [integral_const,probReal_univ,one_smul,add_sub_cancel_left]
    refine Finset.sum_congr rfl fun i _ => integral_const_mul ..
  rw [hv]
  apply (norm_sum_le ..).trans
  calc
    _ ≤ ∑ i∈S, ‖F.part (scene i)‖ * η := Finset.sum_le_sum fun i ih => by
      obtain ⟨hj,hk⟩ := Finset.mem_erase.mp ih
      have hh : (scene (s.val \ i)).val.Nonempty := Finset.sdiff_nonempty.mpr (fun hx => hj (le_antisymm (Finset.mem_powerset.mp hk) hx))
      unfold c;rw [norm_mul]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (gets T w _ (raw_in T P hp ..)).trans (ht _ hh)
    _ ≤ _ := by
      rw [← Finset.sum_mul]
      refine mul_le_mul_of_nonneg_right ?_ he
      have he : Poly.price (fun _ => 1) F = ∑ i : modes V, ‖F.part i‖ := by simp [Poly.price,Poly.toll]
      rw [he, show (∑ i∈S, ‖F.part (scene i)‖) = ∑ i ∈ S.image scene, ‖F.part i‖ from
        Eq.symm (Finset.sum_image (fun _ _ _ _ h => (same_scene ..).mp h))]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => norm_nonneg _)
end cell

section
variable (C : Family G) (x : Points n) (B : Fin n → (standard C).Tag)

def maxProfile := profile (standard C) B x

def cumulants (hx : x∈conf n) : veil (Fin n) := connected (maxProfile C x B) (profile_vac _ (Maxwell.table_regular C.labels) _ hx _)
lemma cumulative (hx : x∈conf n) : Expands (cumulants C x B hx) (maxProfile C x B) := connected_spec ..


variable (N p k : ℕ) (u : Fin n → Cover) (t : Fin n → C.book.Token)

def probes (i : Fin n) := C.seen (t i) (Cells.location C.S k N p (u i))



variable {C B x N p u t k}

lemma probes_cont (i : Fin n) : Continuous (probes C N p k u t i) := C.continuousO N p (t i).1 (t i).2 _



theorem full_cost (h : C.Makes) (hx : x∈conf n) {η : ℝ} (hη : 0≤η) (T : Tiling (C.side N p))
    (hp : ∀ i, Interior (T.chamber 0) (probes C N p k u t i))
    (he : ∀ s : modes (Fin n),s.val.Nonempty → T.rootTest (C.beta N p)
      (fun U => (cylinder (cumulants C x B hx) (probes C N p k u t) U).part s) ≤ η) :
    ‖C.numeric N p t (fun i => Cells.location C.S k N p (u i)) -
      (standard C).useAt (standard C) x B‖ ≤ Poly.price (fun _ => 1) (maxProfile C x B) * η := by
  have hi := Read.maxwell T _ η (seamless h ..) (cumulative _ _ _ _) hp hη he (scene Finset.univ)
  unfold maxProfile at hi; rw [profile_full _ (Maxwell.table_sym C.labels) _ hx] at hi; rw [Family.num]
  exact hi
end
end YM.Next.Rank.Read
