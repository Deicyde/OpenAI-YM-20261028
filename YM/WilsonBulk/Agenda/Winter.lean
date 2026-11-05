import YM.WilsonBulk.Agenda.Edges

/-!
# Post-block finite bills (Charges) -- single pressure bond pricing only; no lifetime assumptions.
    Needed to phrase what schedule would actually pay. Prove can be prepared at all L and fixed
    earlier width gates. Orders finite increments in JLook. Consumers operate under *Land* whose
    price uses `age` polynomial. Here natural prerequisites includes stronger post lease.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Parapet.Agenda
open Function Filter Lattice Laurent RG Schedule Finset Precision Exterior Stationary Audience Recall Pert.Bulk Sheet Atelier Bloch Work.F08
open scoped Topology Classical ENNReal BigOperators
variable {G : Gauge} {K : KernelChoices} {F : MapPrices} {P : Patch} {i j k n E : ℕ} {x a p σ θ μ w C : ℝ} {L : Side}
variable {J : ChartRatio G} {R : Model P K} {U : Lit G K F}
abbrev lampCost (P : Patch) (G : Gauge) (σ : ℝ) (E : ℕ) (C : ℝ) := lane P (Cloth G) (Cloth G) σ (E+2)*C
abbrev cape (P : Patch) (G : Gauge) (C : ℝ) := hood (Echelon (Cloth G) (Cloth G) P.L) (Cloth G) * C
structure Charges (V : Lit G K F) (R : Model P K) (J : ChartRatio G) (i E : ℕ) (w C : ℝ) : Prop where
  warm : Warm P K J (V.width E P.J) (V.width E i) (V.gamma P.J) (SeenRank F G i) E C
  lamp : 1 ≤ w
  poles (A : Levels G) (H : Horizon A) : H.Suffices F → ∀ m N,m≤N→ stage A m=P.J → Serves G R (H.H N m) (V.gamma P.J) w
  spark : (flare G P).strip (V.gamma P.J) w
  react : (phiPart G R).strip (V.gamma P.J) w
  tickets : w≤ C ∧ |F.Ω i| ≤ C ∧ |F.Ω P.J| ≤ C ∧ beam_cap P G K w ≤ C ∧ lanternFull P G w (F.Ω P.J) ≤ C ∧ kcap F i ≤ C
  costs_turn : lampCost P G (V.width E i) E |F.Ω P.J| ≤ C ∧ lampCost P G (V.width E i) E (beam_cap P G K w) ≤ C ∧ lampCost P G (V.width E i) E (lanternFull P G w (F.Ω P.J)) ≤ C ∧ cape P G (max (beam_cap P G K w) 1) ≤ C ∧ guidesN P G*w ≤ C
  pricing : greenFace P G w ≤ C ∧ greenTurn P G K w ≤ C ∧ lampCost P G (V.width E i) E (greenTurn P G K w) ≤ C ∧ cape P G (greenTurn P G K w) ≤ C ∧ guidesN P G*greenFace P G w ≤ C ∧ oxidize G 1 ≤ C
  widths : (V.width E i)⁻¹ ≤ C ∧ (V.gamma P.J)⁻¹ ≤ C ∧ (αflat F i)⁻¹ ≤ C ∧ (P.L.val:ℝ) ≤ C
abbrev Charge (V : Lit G K F) (R : Model P K) (J : ChartRatio G) (i E : ℕ) (C : ℝ) := ∃ w,Charges V R J i E w C
lemma Lit.charge (V : Lit G K F) (R : Model P K) (J : ChartRatio G) (h : Threshold V a i P.J P.L E) (hp : P.Branches K G) : ∀ᶠ C:ℝ in atTop, Charge V R J i E C := by
  obtain ⟨u,hu,hF,hU⟩:= V.Forecast P hp R; obtain ⟨v,hv,hV⟩:= (Stamped.phi G R).bound (V.gamma P.J); let w : ℝ:=u+v+1; have hw : u≤w:= by unfold w; linarith
  have hx : v ≤ w:= by unfold w; linarith
  have hh : 1≤w:= by unfold w; linarith
  let A:= lanternFull P G w (F.Ω P.J); let B:= beam_cap P G K w; let f:=lampCost P G (V.width E i) E; let g:=cape P G; let x:=greenFace P G w; let y:=greenTurn P G K w
  filter_upwards [warm_eventually P K J (SeenRank F G i) h.season,eventually_ge_atTop w,eventually_ge_atTop |F.Ω i|, eventually_ge_atTop |F.Ω P.J|, eventually_ge_atTop B, eventually_ge_atTop A,eventually_ge_atTop (kcap F i),eventually_ge_atTop (f |F.Ω P.J|),eventually_ge_atTop (f B), eventually_ge_atTop (f A), eventually_ge_atTop (g (max B 1)), eventually_ge_atTop (guidesN P G*w), eventually_ge_atTop x, eventually_ge_atTop y, eventually_ge_atTop (f y), eventually_ge_atTop (g y), eventually_ge_atTop (guidesN P G*x), eventually_ge_atTop (oxidize G 1), eventually_ge_atTop ((V.width E i)⁻¹), eventually_ge_atTop ((V.gamma P.J)⁻¹), eventually_ge_atTop ((αflat F i)⁻¹), eventually_ge_atTop (P.L.val:ℝ)] with C hc h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21
  exact ⟨w,hc,hh,fun A H h i j h' he=> (hU A H h i j h' he).lower le_rfl hw, strip_mono hF le_rfl hw, strip_mono hV le_rfl hx, ⟨h1,h2,h3,h4,h5,h6⟩,⟨h7,h8,h9,h10,h11⟩,⟨h12,h13,h14,h15,h16,h17⟩,⟨h18,h19,h20,h21⟩⟩
lemma Charge.more (h : Charge U R J i E C) (he : C≤x) : Charge U R J i E x := by
  obtain ⟨w,hc,h1,h2,h3,h4,⟨h5,h6,h7,h8,h9,h19⟩,⟨hx,hA,hB,hM,hF⟩,⟨h10,h11,h12,h13,h14,h15⟩,⟨h16,h17,h18,h20⟩⟩:= h
  exact ⟨w,hc.more he,h1,h2,h3,h4, ⟨h5.trans he,h6.trans he,h7.trans he,h8.trans he,h9.trans he,h19.trans he⟩,⟨hx.trans he,hA.trans he,hB.trans he,hM.trans he,hF.trans he⟩,⟨h10.trans he,h11.trans he,h12.trans he,h13.trans he,h14.trans he,h15.trans he⟩,⟨h16.trans he,h17.trans he,h18.trans he,h20.trans he⟩⟩
-- symbolic prescription eventually depends on σ,γ,λ,J etc. Not an overlap or land premise

def postTranche (V : Lit G K F) (R : Model P K) (J : ChartRatio G) (i E : ℕ) (a : ℝ) := if h: Threshold V a i P.J P.L E ∧ P.Branches K G then (eventually_atTop.mp (V.charge R J h.1 h.2)).choose else 1
lemma post_force (h : Threshold U a i P.J P.L E) (hp : P.Branches K G) (he : postTranche U R J i E a ≤ x) : Charge U R J i E x := by rw [postTranche,dif_pos ⟨h,hp⟩] at he; exact (eventually_atTop.mp (U.charge R J h hp)).choose_spec _ he

lemma RequestLead (H : Charge U R J i E C) : (P.L.val:ℝ) ≤ C := H.elim (fun _ hw=>hw.widths.2.2.2)
lemma WidthRate (H : Charge U R J i E C) : (U.width E i)⁻¹ ≤ C := H.elim (fun _ hw=>hw.widths.1)
lemma FlatCash (H : Charge U R J i E C) : kcap F i ≤ C:= H.elim (fun _ hw=>hw.tickets.2.2.2.2.2)

variable {A : Levels G} {H : Horizon A} {ℓ m N : ℕ}
def Sized (U : Lit G A.clock.kernel F) (ℓ : ℕ) (a : ℝ) (E : ℕ) := ∀ i ≥ ℓ,5 ≤ stage A (i+1) ∧ Threshold U a (stage A i) (stage A (i+1)) (A.S.block i) E
lemma axle (A : Levels G) (i : ℕ) : after (stage A i) (stage A (i+1)) := ⟨A.fits.mono (by omega : i ≤ i+1),A.fits.stepSlow i⟩
abbrev lureFlat (A : Levels G) (F : MapPrices) m := αflat F (stage A m)
variable {U : Lit G A.clock.kernel F}
lemma admit_request (he : Sized U ℓ a E) : FlatRequest A F F ℓ (lureFlat A F) a:= by
  refine ⟨fun m hm=>(he m hm).1,fun i _=>positive _ _,fun i _=> ?_,fun i hi=>(he i hi).2.keep,fun i hi=> (he i hi).2.hess_large⟩ -- lost `hi`
  · have hh: (stage A (i+1))=stage A i ∨ stage A (i+1) = stage A i+1:= by have ⟨hy,hx⟩:= axle A i; omega
    simp only [min_self]; refine ⟨min_le_left ..,?_⟩; rcases hh with hh|hh <;> rw [hh]; exact min_le_left ..
    exact min_le_right ..
end YM.WilsonBulk.Parapet.Agenda
