import YM.Planned.PRIMARY_INTEGRAL_295.Dials
import YM.Planned.PRIMARY_INTEGRAL_295.Racks


/-!
# torus-patched **b** certificate earned for Journey queries

One real cut extending actual path log, no masking schedule inserted.

Cut
radius r AFTER L before anchors with Wisdom (r contains all required).

Per output bond e estimates pe weighted START as in p threshold p.power,
needed at Lxe stationary comparision.

No row values outside agreement asserted, full cutoff explicitly zero.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Cabins
open Function Filter Set Metric MeasureTheory ProbabilityTheory
open Labels Lattice RG Wilson Source Source.Drops Oval Nimbuses Dunes Place
open Precision Exterior Tree Streets Porous Carrier Bloch Next.Free Progress.StationaryScenes  Bazaars Launch Shapes
open WardBin.Lies WardBin.Wheels Racks Dials
open scoped Topology ContDiff BigOperators NNReal Classical Matrix.Norms.Frobenius
variable {E I : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype I]
variable {G : Gauge} {T : Finset Cover} {k l d : ℕ} {t ξ s M δ u : ℝ} {F : Labels.Frame G d} {c f : Side}
variable {S : StepData c f}

section Cabin
-- syntax `z` coarse transform. prefix all y path.
variable (t) (z:Site c→G.El) (r : ℕ) (p : E→Config G c)
def room (e:Edge (Site c)) (y:E) := if separation 0 e.1 ≤ r then t⁻¹ • G.plog (G.mat (Lattice.gauge z (p y) e)) else 0

def patched (y:E) : Dir G c := fun i=>room t z r p ((Work.E03.poleEquiv c).symm i) y
omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma symbolic (i:Edge (Site c)) (y:E): patched t z r p y (Work.E03.poleEquiv c i)= room t z r p i y := by
   unfold patched; rw [Equiv.symm_apply_apply]

-- Queries need all p including the support endpoints if pricing re-HE. Caller
-- cuts extend by margin elsewhere. Ready for E chart trajectory: assert
-- agreement of PU selector & final branches on larger support separately.
def Saddle (b:E→Dir G c) : Prop :=
   ∀ᶠ y:E in 𝓝 0, ∀ e:Edge (Site c), separation 0 e.1 ≤ r →
      Lattice.gauge z (p y) e=represent (t • b y) e ∧
       G.plog (G.mat (Lattice.gauge z (p y) e))= t • b y (Work.E03.poleEquiv c e)

def Trail (g:Ratio c f) (T:SectionData F) (r:ℕ) :=
    ∀ y ∈ T.footprint (0:Site f), separation 0 (g.parent y) ≤ r
omit [NormedSpace ℝ E] in
lemma Saddle.agrees (g:Ratio c f) (T:SectionData F) {b} (h : Saddle t z r p b) (ht : Trail g T r) :
    ∀ᶠ x in 𝓝 0, ∃ z:Site c→G.El, Agrees (T.footprint (0:Site f)) (replica g (Lattice.gauge z (p x))) (replica g (represent (t • b x))) := by
    filter_upwards [h] with x hx; refine ⟨z,fun i hi hp=>?_⟩; unfold replica; split_ifs
    · rfl
    exact (hx (g.parent i.1,i.2) (ht _ hi)).1

omit [NormedSpace ℝ E] in
lemma bridle {B:ℕ} (K:Knurls G B) (h:0<t) (he:∀ i:Edge (Site c), separation 0 i.1≤r → ∀ᶠ y in 𝓝 0,G.chord (Lattice.gauge z (p y) i)≤2*K.r) :
      Saddle t z r p (patched t z r p) := by
   have hy (i:Edge (Site c)) : ∀ᶠ y in 𝓝 0,separation 0 i.1 ≤ r → G.chord (Lattice.gauge z (p y) i)≤2*K.r:= by
     by_cases hH:separation 0 i.1 ≤ r
     · filter_upwards [he i hH] with y hy _; exact hy
     exact Eventually.of_forall (fun y hy=>False.elim (hH hy))
   filter_upwards [(eventually_all ..).mpr hy] with y hy i hi
   have hh : t • patched t z r p y (Work.E03.poleEquiv c i) = G.plog (G.mat (Lattice.gauge z (p y) i)):=by
      simp only [symbolic,room,if_pos hi,smul_inv_smul₀ h.ne']
   refine ⟨?_,hh.symm⟩; change _=G.lieExp (t • patched t z r p y (Work.E03.poleEquiv c i))*1
   rw [mul_one,hh]; exact (K.sparks _ (hy i hi)).1.symm
end Cabin

-- Torus-to-cover shape accounting
lemma spans (x:Cover) (c:Side) : separation 0 (wrap c x) ≤ Laurent.size x := by
    rw [separation_comm,separation,sub_zero]; exact within_size x c

section Moods
-- per e pre. post Hull radius multiplies via explicit post appraisal.
def hcount : ℝ:= Fintype.card PlaqAxes
lemma hcount_pos: 0≤hcount:=Nat.cast_nonneg _
def price1 (π : ℝ) (K:Knurls G k) := K.C*π*(1+4*hcount)
def marked (r a : ℕ) := (1+(r:ℝ))^a

def roofs (K:Knurls G k) (π:ℝ) (r a:ℕ) := price1 π K * marked r a^(k+1)

variable {r:ℕ} {U:Config G c} {A : Slab G c k} {P:BudgetPoint} {X:Support c}

-- r used, circle(r+1) costs before derivative earning. budget holder K
-- may cover larger orders. Monotone reductions okay.
structure Plaza (P : BudgetPoint) (π:ℝ) (K:Knurls G k) (t:ℝ) (X:Support c) (r:ℕ) : Prop where
    inject : 2*(r+1)<c.val
    circle : ∀ y : Site c, separation 0 y ≤r+1 → y∈X
    bHealth : PPX.Blend π t P.threshold
    girder : 4*(1+(r:ℝ))*(hcount*P.threshold) ≤ K.r

variable {π:ℝ} (K : Knurls G k) (o:Lattice.Order) (ha : ∀ i, P.dirBound 0 (A i)) (hu:Healthy P.threshold X U) (hB:Plaza P π K t X r)

def leading (o:Lattice.Order) (t:ℝ) (r:ℕ) (U:Config G c) (A:Slab G c k) := patched t (cardAt o U) r (journey U k A)

include hB hu




include ha



omit ha hu hB in
private lemma card_ge {π : ℝ} (K:Knurls G k) (hπ : 1≤π):1≤price1 π K:=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le K.cap hπ) (le_add_of_nonneg_right (mul_nonneg (by positivity) hcount_pos))

omit ha hu hB in
private lemma cart_one (i:Fin k): ‖cart i‖≤1:= (pi_norm_le_iff_of_nonneg zero_le_one).2 (fun j=> by simp [cart, Pi.single_apply]; split_ifs <;> simp)


end Moods
end YM.Planned.PrimaryIntegral295.Cabins
