import YM.Next.WARD_BIN.Hats
import YM.Push.CUTOFF_PROJECTORS.Price
import YM.Push.RELAY_DIFFERENCE.Stencils
import YM.Push.STRESS_FLUX.Haar




/-!
# Erased finite calls for the same equation campaign

Pay the Wilson part, not assuming `exactOnSep` nor a small-error feature,
without replacing Campaign weights by those from the separate WARD_BIN
Chart (other normalization). Use it with RelayDifference finite mode bills. Per packet and no period restriction except the
input itself hitting its stencil. LEFT divergence term essential; the
reference readout/cost is from the calibrated `.chain`, not the cheap
formula you'd get just using the top equation polynomial, and uses C's
actual β and ĉ.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.PhysicalPeriodLimitF933.Equations
open Function Filter Set MeasureTheory Lattice RG Wilson Extraction Extraction.Lease
  Push.CutoffProjectors Push.RelayDifference Packet StressFlux Source Bid
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G : Gauge} {C : Family G} {N p d : ℕ} {W : Worth} {f : Extraction.Order} {X : Finset Cover}

lemma forwards (e : Edge (Site (C.side N p))) (j : G.ColorIndex) (z : ℝ) (U : Config G (C.side N p)) :
    increment U (z • Packet.forward e j)=bump e.1 (posDir e.2) (StressFlux.orth j) z U := by
  funext x
  by_cases h : x=e
  · subst x; simp [increment,Packet.forward,bump,StressFlux.modify,posDir,Step.used,orth]
  simp [increment,Packet.forward,bump,StressFlux.modify,posDir,Step.used, h]

lemma deriva (e : Edge (Site (C.side N p))) (j : G.ColorIndex) {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (h : Config G (C.side N p) → Y) :
    Packet.derivative h e j = Dlink e.1 (posDir e.2) (StressFlux.orth j) h := by
  funext U; unfold Packet.derivative Dlink; simp [leftDerivs,forwards (C:=C)]

lemma along {E : Packet C d N p} (h : E.ComesFrom X) (w : equationSpace (C.labels.level d)) (e : Edge (Site (C.side N p))) (j : G.ColorIndex) :
    Varies e.1 (posDir e.2) (StressFlux.orth j) (fun U => E.X w U e j) := by
  obtain ⟨H,h1,h2⟩ := h.coefficients w e j
  refine ⟨tame_of_continuous H,tame_of_continuous (deriva (C:=C) e j (fun U => E.X w U e j) ▸ h2 e j),fun U => ?_⟩
  have he := h1 e j U
  simp_rw [forwards (C:=C), deriva (C:=C) e j] at he; exact he

lemma energy_read (e : Edge (Site (C.side N p))) (j : G.ColorIndex) (U : Config G (C.side N p)) :
    Packet.derivative energy e j U = inner ℝ (StressFlux.orth j) (StressFlux.force U e.1 (posDir e.2)) := by
  rw [deriva (C:=C)]; exact (energy_bump_zero _ _ _ _).deriv

variable {E : Packet C d N p} (hE : E.ComesFrom X) (v : equationSpace (C.labels.level d))

include hE
lemma score (e : Edge (Site (C.side N p))) (j : G.ColorIndex) {B : Config G (C.side N p) → ℂ}
    (hB : Varies e.1 (posDir e.2) (StressFlux.orth j) B) :
    moment (C.beta N p) (fun U =>
      (E.X v U e j * (Packet.derivative energy e j U : ℝ) -
          ((C.beta N p : ℂ))⁻¹ * Packet.derivative (fun V => E.X v V e j) e j U)*B U) =
      ((C.beta N p : ℂ))⁻¹ * moment (C.beta N p)
        (fun U => E.X v U e j * Packet.derivative B e j U) := by
  let β := C.beta N p
  let S := fun U => E.X v U e j
  have hw (U) : S U * (Packet.derivative energy e j U : ℝ) - ((β:ℂ))⁻¹ * Packet.derivative S e j U =
      (β:ℂ)⁻¹ * StressFlux.insertion β e.1 (posDir e.2) (orth j) S U := by
    have hb : (β : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hE.coupling.ne'
    unfold StressFlux.insertion
    rw [energy_read (C:=C),deriva (C:=C),Complex.ofReal_mul]
    field_simp
  change (moment β fun U => (S U * (Packet.derivative energy e j U : ℝ) - (β:ℂ)⁻¹*Packet.derivative S e j U)*B U)=_
  simp_rw [hw,mul_assoc ((↑β:ℂ)⁻¹)]
  unfold moment; rw [integral_const_mul, ← moment, insertion_moment (along hE v e j) hB]
  rw [deriva (C:=C)]
  rfl

lemma score_whole (B : Config G (C.side N p) → ℂ) (hB : ∀ e : Edge (Site (C.side N p)), ∀ j : G.ColorIndex,
      Varies e.1 (posDir e.2) (StressFlux.orth j) B) :
    moment (C.beta N p) (fun U => E.Jorigin v U * B U) =
    ((C.S.a N : ℂ)^d)⁻¹ * ((C.beta N p : ℂ))⁻¹ *
      ∑ e : Edge (Site (C.side N p)), ∑ j : G.ColorIndex,
        moment (C.beta N p) (fun U => E.X v U e j * Packet.derivative B e j U) := by
  classical
  let g (e : Edge (Site (C.side N p))) (j : G.ColorIndex) (U : Config G (C.side N p)) := E.X v U e j * ((Packet.derivative energy e j U:ℝ):ℂ) - ((C.beta N p:ℂ))⁻¹*Packet.derivative (fun V => E.X v V e j) e j U
  have hg e j : Continuous (g e j) := (((hE.coefficients ..).continuous).mul (Complex.continuous_ofReal.comp (hE.action.rate e j))).sub
    (continuous_const.mul ((hE.coefficients v e j).rate e j))
  have ht (e j) : Integrable (fun U => g e j U * B U) (law G _ (C.beta N p)) := Tame.int ((tame_of_continuous (hg e j)).mul (hB e j).tame) _
  unfold Packet.Jorigin
  change moment _ (fun U => ((C.S.a N:ℂ)^d)⁻¹ * (∑ e, ∑ j, g e j U) * B U)=_
  simp_rw [mul_assoc (_⁻¹) (Finset.sum _ _),Finset.sum_mul, moment,integral_const_mul,
    integral_finsetSum _ (fun e _ => integrable_finsetSum _ (fun j _ => ht e j))]
  have he e j := score hE v e j (hB e j)
  change ∀ e : Edge (Site (C.side N p)), ∀ j : G.ColorIndex, moment (C.beta N p) (fun U => g e j U * B U)=_ at he
  unfold moment at he
  simp_rw [integral_finsetSum _ (fun j _ => ht _ j), he,Finset.mul_sum, mul_assoc]

/-- Separated cutoff phase, no retuned coordinates. Using the whole
conditional identity enables repaying it WITH contact terms in other calls as
well. On Wilson stencil spectators no masks or α can be skipped. -/
lemma score_local {O : Set (Site (C.side N p))} (hX : Disjoint (↑(Packet.sites (C.side N p) X) : Set _) O) (B : Config G (C.side N p) → ℂ) (h : RegularD B) (hB : LocalOn O B) :
    moment (C.beta N p) (fun U => E.Jorigin v U * B U)=0 := by
  rw [score_whole hE v B (fun _ _ => h.varies)]
  suffices hh : ∀ (e : Edge (Site (C.side N p))) (j : G.ColorIndex) (U), E.X v U e j * Packet.derivative B e j U = 0 by
    simp_rw [hh]; simp [moment]
  intro e j U
  by_cases hx : E.X v U e j = 0; simp [hx]
  have he : e.1∈Packet.sites (C.side N p) X := (hE.moves v U e j hx).1
  rw [deriva (C:=C), Dlink_off hB (Or.inl (Set.disjoint_left.mp hX he))]; simp


omit hE in
lemma moves (t b : Site (C.side N p)) (U : Config G (C.side N p)) :
    translate t (translate b U)=translate (t+b) U := by unfold Lattice.translate; simp [add_assoc]

omit hE in
/-- `J` is entirely translated, not just the derivative summands
independently (that would effectively keep a reference mask in the origin cell). -/
lemma marked_shift (t b : Site (C.side N p)) (U : Config G (C.side N p)) :
    E.J v (t+b) U = E.J v t (translate b U) := by unfold Packet.J; rw [moves (C:=C)]

lemma fitted : Local X (E.J v) := by
  refine ⟨fun t b => ?_,fun t => ?_⟩
  · funext U; exact marked_shift (E:=E) v t b U
  have hc : Continuous (E.J v t) := (hE.continuous v).comp (show Continuous (translate t (K:=G.El)) by unfold Lattice.translate; fun_prop)
  refine ⟨fun k U => ?_,hc.measurable,?_,hc.bounded_above_of_compact_support (HasCompactSupport.of_compactSpace _)⟩
  · unfold Packet.J
    have he : translate t (Lattice.gauge k U) = Lattice.gauge (fun i => k (i+t)) (translate t U) := by
      unfold Lattice.translate Lattice.gauge; simp only [add_comm _ t,add_assoc]
    rw [he,hE.gauge v]
  intro U V hu
  exact hE.reads v _ _ (fun e he hp => by
    have ht a (ha : a ∈ Packet.sites (C.side N p) X) : a+t ∈ stamp X t := by
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
      exact Finset.mem_image_of_mem _ hx
    have hm : e.1+t+Lattice.step e.2∈stamp X t := add_right_comm e.1 _ _ ▸ ht _ hp
    exact hu (e.1+t,e.2) (ht _ he) hm)

/-- Moving spectator lists pay eventually even if coefficient values
blow at this period. Uniformity needed only on D04 query i,δ,q.
No benefit here from minima assertions or weak matching. -/
lemma erasure {n : ℕ} (i : Fin n) (q : Fin n → C.book.Token) (y : Fin n → Site (C.side N p))
    (ht : ∀ j : Fin n, j≠i → Disjoint (Packet.sites _ X)
      ((C.localSection (q j).1).footprint (y j - y i))) :
    moment (C.beta N p) (fun U => ∏ j : Fin n, if j=i then E.J v (y i) U else C.seen (q j) (y j) U) = 0 := by
  classical
  let s := Finset.univ.erase i
  let V := fun j => C.seen (q j) (y j - y i)
  let B (U : Config G (C.side N p)) := ∏ j ∈ s,V j U
  let O : Finset _ := s.biUnion fun j => (C.localSection (q j).1).footprint (y j - y i)
  have hd : Disjoint (↑(Packet.sites (C.side N p) X) : Set (Site (C.side N p))) (O : Set _) := by
    refine Set.disjoint_left.mpr fun a hb hh => ?_
    obtain ⟨j,hj,h⟩ := Finset.mem_biUnion.mp (show a∈O from hh)
    exact Finset.disjoint_left.mp (ht j (Finset.mem_erase.mp hj).1) hb h
  have hl : LocalOn (O : Set (Site (C.side N p))) B := by
    intro U P h
    refine Finset.prod_congr rfl fun j hj => C.localO _ _ _ (q j).2 _ _ _ (agrees_mono h ?_)
    exact fun _ hi => Finset.mem_biUnion.mpr ⟨j,hj,hi⟩
  have hf : RegularD B := regular_word ..
  have hh := score_local hE v hd B hf hl
  let a : Config G (C.side N p) → ℂ := fun U => E.Jorigin v U * B U
  have hI : Integrable a (Wilson.law G _ (C.beta N p)) := continuous_integrable _ ((hE.continuous v).mul hf.cont)
  rw [← hh, ← moment_pull _ 1 (y i) a hI]
  congr 1; funext U
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),if_pos rfl,Function.comp_apply,pull_one]
  unfold a Packet.J B; congr 1
  exact Finset.prod_congr rfl (fun j hj => by
    rw [if_neg (Finset.mem_erase.mp hj).1]; unfold V Family.seen; rw [C.translation,sub_add_cancel])

omit hE in
lemma far {n : ℕ} (i : Fin n) (q : Fin n → C.book.Token) (δ : ℝ) (hδ : 0 < δ) (X : Finset Cover) :
    ∀ᶠ N : ℕ in atTop, ∀ p, ∀ x : Fin n → Site (C.side N p),
      (∀ j k : Fin n, j ≠ k → δ ≤ C.S.a N * separation (x j) (x k)) →
      ∀ j : Fin n, j≠i → Disjoint (Packet.sites (C.side N p) X)
        ((C.localSection (q j).1).footprint (x j-x i)) := by
  let M := fun j => (C.localSection (q j).1).stencil
  let w := WardBin.cord X
  let t := fun j => WardBin.cord (M j)
  have H j : ∀ᶠ N in atTop, C.S.a N * ((w:ℝ)+ t j) < δ := by
    refine (show Tendsto (fun N => C.S.a N*((w:ℝ)+ t j)) atTop (𝓝 0) from ?_).eventually (gt_mem_nhds hδ)
    simpa using C.S.shrinks.mul_const ((w:ℝ)+t j)
  filter_upwards [eventually_all.mpr H] with N H p x hb j hj
  apply Finset.disjoint_left.mpr; intro a h1 h2
  obtain ⟨b,hb',rfl⟩ := Finset.mem_image.mp h1
  let o := wrap (C.side N p) b
  have h4 : o∈halo (t j) {x j-x i} := WardBin.contained _ _ h2
  have hw : o∈halo w (n:=C.side N p) {0} := WardBin.contained X 0 (Finset.mem_image.mpr ⟨b,hb',add_zero _⟩)
  obtain ⟨s,hs,hS⟩ := halo_spec.mp h4
  obtain ⟨r,hr,hR⟩ := halo_spec.mp hw
  rw [Finset.mem_singleton.mp hr] at hR
  rw [Finset.mem_singleton.mp hs, separation_comm] at hS
  have hh := (separation_triangle (0:Site _) o (x j-x i)).trans (add_le_add hR hS)
  rw [separation_comm 0, separation,sub_zero] at hh
  have he : (separation (x j) (x i):ℝ) ≤ ↑w + ↑(t j) := by exact_mod_cast hh
  exact (H j).not_ge ((hb j i hj).trans (mul_le_mul_of_nonneg_left he (C.S.a_pos _).le))

variable (A : Campaign C) (w : Campaign.Descriptions C d)
omit hE in
theorem delivers : Stencilled f (A.equationTrial w) ∧ exactOnSep C f (A.equationTrial w) := by
  have H := A.auth_late d f
  refine ⟨⟨A.box d, ((Extraction.Order.fused f _).mpr H).mono fun i hi => fitted hi (w i)⟩,fun n q i δ hδ => ?_⟩
  refine H.mono fun k h => ?_
  filter_upwards [h, f.mesh.cofinal.eventually (far i q δ hδ (A.box d))] with j h hi y he
  let N := f.mesh j; let p := f.per k
  exact erasure h (w (N,p)) i q y (hi p y he)
end YM.Further.PhysicalPeriodLimitF933.Equations
