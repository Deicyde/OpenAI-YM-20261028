import YM.Extra.MULTISOURCE_TRAJECTORIES.Hangers

/-!
# Preparing a calibrated/reference family with a common aperture

An explicit option for the original production of a family, if needed.
State precisely what is preserved, instead of identifying two families or
pretending an arbitrary retention predicate must be stable. Do not silently
apply this change later to an already running physical witness. The padded
family uses the transported factory, relabelled reps and exact same sections,
levels and O (no re-shooting).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Trajectories.Hangers
open RG Wilson Lattice Function Finset MeasureTheory Filter Source Labels RG.Shoot Input
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G : Gauge} {n : Side} {H : History G} {d : ℕ} {F : Frame G d} {N p : ℕ}

def coeff (A : Coefficient F n) : Coefficient F n := { A with forced := shift A.forced n }

lemma format {A : Coefficient F n} {o : Site n} {T : Hol G} {P : Rep G n} (h : A.Format o T P) : (coeff A).Format o T (rep P) := by
  refine ⟨h.smooth,h.origin,h.identity_null,h.projects,?_,?_,?_,?_,?_⟩ <;>
    intro j <;> dsimp only [coeff, rep, entries,shift] <;> cases (numbers n).symm j
  · exact h.forcing _
  · simp
  · exact h.carried _
  · simp
  · exact h.invariant _
  · exact fun _ _ => rfl
  · exact h.supported _
  · exact fun _ _ _ _ => rfl
  · exact h.borel _
  exact measurable_const

lemma rem_bound {A : Coefficient F n} {o : Site n} {P : Rep G n} {w u : ℝ} (h : A.remBound o P w u) : (coeff A).remBound o (rep P) w u := by
  obtain ⟨a,b,ha,hb,h1,h2,h3,k,h4,h5⟩ := h
  have he i : 0 ≤ shift k n i ∧ ∀ U,‖shift A.forced n i U‖ ≤ shift k n i := by unfold shift; cases (numbers n).symm i; exact h5 _; simp
  refine ⟨a,b,ha,hb,h1,h2,h3,k |> (shift · n),budget_image (named n).injective injective_id (fun j => mul_nonneg (Real.exp_pos _).le (he j).1) (fun j hj => ?_) h4 (fun j => ?_), he⟩
  · simp [shift_zero k hj,BudgetPoint.mass]
  exact le_of_eq (by dsimp only [id_eq,rep]; rw [forced,shift_in])

lemma marked_rep (A : Coefficient F n) (P : Rep G n) (U : Config G n) (s : Finset ℕ) :
    (coeff A).marked (rep P) (s.map (named n)) U = A.marked P s U := by
  rw [Coefficient.marked,Coefficient.marked]
  dsimp only [rep]
  by_cases he : P.activities.admissible P.p U s
  swap; · rw [if_neg he,if_neg (mt (admissible ..).mp he)]
  rw [if_pos he,if_pos ((admissible ..).mpr he),sum_map]; refine sum_congr rfl fun j _ => ?_
  rw [← map_erase,prod_map]; simp only [coeff,entries,shift_in]

lemma coefficient_density (P : Rep G n) (D : SectionData F) (A : Coefficient F n) (o : Site n) :
    (coeff A).density o D (rep P) = A.density o D P := by
  funext U
  unfold Coefficient.density; rw [density]; congr 2
  rw [← (map_injective (named n)).tsum_eq (fun t ht => by
    change (coeff A).marked (rep P) t U ≠ 0 at ht
    by_contra hh
    apply ht; obtain ⟨j,hj,hj'⟩ := zero_outside hh; rw [Coefficient.marked]; split; swap; rfl
    refine sum_eq_zero fun i hi => ?_; by_cases hij : i=j
    · subst i; simp [coeff, shift_zero A.forced hj']
    have hz := prod_eq_zero (M₀:=ℂ) (mem_erase.mpr ⟨Ne.symm hij,hj⟩) (f:=fun k => ((rep P).activities.K k U :ℂ))
      (by simp [rep,entries,shift_zero P.activities.K hj'])
    rw [hz,mul_zero])]
  exact tsum_congr (marked_rep A P U)

lemma shift_linear {ι M : Type*} [AddCommGroup ι] [Module ℂ ι] [AddCommGroup M] [Module ℂ M] {f : ι → ℕ → M} (n : Side)
    (hf : IsLinearMap ℂ f) : IsLinearMap ℂ (fun x => shift (f x) n) := by
  constructor <;> intro a b <;> funext i
  · rw [hf.map_add]; unfold shift; rw [Pi.add_apply]; cases (numbers n).symm i <;> simp
  rw [hf.map_smul]; unfold shift; rw [Pi.smul_apply]; cases (numbers n).symm i <;> simp

def transfer (T : TransferData F H N p) : TransferData F (history H) N p := {entries := fun m v => coeff (T.entries m v),terminal:=T.terminal}
lemma based {C : Hol G} {D : SectionData F} {T : TransferData F H N p} {r : ℕ} (h : T.Based C D r) : (transfer T).Based C D r where
  ref := h.ref
  format m hr hm v := format (h.format m hr hm v)
  cap m hr hm v := rem_bound (h.cap m hr hm v)
  back := h.back
  front := h.front
  linear m hr hm := let he := h.linear m hr hm; ⟨he.1,he.2.1,shift_linear _ he.2.2.1,he.2.2.2⟩
  bare_coord := h.bare_coord
  bare_germ := h.bare_germ
  encode v U := by dsimp only [history,transfer]; rw [coefficient_density,density]; exact h.encode v U
  unnormalized m hr hm v := by dsimp only [history,transfer]; rw [coefficient_density,coefficient_density]; exact h.unnormalized m hr hm v
  reads := h.reads
  unit_coord := h.unit_coord
  realForm := h.realForm
  orients := h.orients


variable (C : Family G)




section Directed
open Precision Supply
variable {S : Sheet G} {D : Rolls S} {T : Protection D} {W : Delays T} {Y : Bar W} {I : Wait Y} {O : ChartRatio G} {K : MapPrices} {P : PostCost D}
def directed (B : Directed G I O K P) : Directed G I O K P :=
    { B with bake := {B.bake with retain := fun _ _ _ _ => True, next := fun _ _ _ _ _ => True, first := fun _ _ _ => True} }
lemma lives {a : Levels G} {R R' : Recipe a} (hr : R.path = R'.path) {N j p} {u : Rep G (a.S.side j p)}
    (h : Lives R N j p u) (h' : R'.retain N j p (rep u)) : Lives R' N j p (rep u) :=
  ⟨h.path.trans (congrFun (congrFun hr _) _),h.point,h.clip,lawful h.valid,h'⟩

lemma comp {B : Directed G I O K P} {u : Trail B.a p} {N} (h : Competes B.bake p N 0 u) : Competes (directed B).bake p N 0 (fun i => rep (u i)) where
  prices i hi hj := let he := h.prices i hi hj; ⟨lives (R:=B.bake) (R':=(directed B).bake) rfl he.1 trivial,he.2⟩
  fromTop := ⟨h.fromTop.scalars,(density ..).trans h.fromTop.raw,trivial⟩
  persists i hi hj := ⟨by rw [density,density]; exact (h.persists i hi hj).link, (h.persists i hi hj).drift,trivial⟩

lemma move {B : Directed G I O K P} {u : Trail B.a p} {N j} (h : B.Move N j p (u j) (u (j+1))) : (directed B).Move N j p (rep (u j)) (rep (u (j+1))) :=
  ⟨by rw [density,density]; exact h.ident,trivial,lives (R:=B.bake) (R':=(directed B).bake) rfl h.bundle trivial,kbound h.forced,h.δ⟩


end Directed
end YM.Extra.Trajectories.Hangers
