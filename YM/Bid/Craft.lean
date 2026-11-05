import YM.Analysis.Polydisc
import YM.Bid.Station

/-!
# Fourier roll and horizons WPs, UNFUNDED

Calls to Vane.analytic in curtain. Hermitian repair in price order using
`Readin/Maintain` only on real phases – analytic verification of Z,CΓ
still a red gate. No history unmasked assumptions infer this property.
Checked usage at lower event at end.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Craft
open Filter Function Lattice RG Wilson Precision Tree Exterior Bloch Laurent Pressure
open YM.Pressure.Stores Matrix
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators NNReal InnerProductSpace ComplexOrder
variable {G : Gauge} {a : Levels G} {c f L : Side}

-- pre index bounds for unmodified pair A,T.
def Donate (T : Towers L) (α C : ℝ) (K : ℕ) := ∀ l : List Axis,l.length ≤ K →
    (advanceC L T.A0 l).strip α (C/(L.val:ℝ)^(1+l.length)) ∧ (advanceC L T.T l).strip α (C/(L.val:ℝ)^(2+l.length))

-- three-form substrate
abbrev C3 := Row (TypeFace 3) (TypeFace 3)

def defect (g : Ratio c f) (H H' : Bed) (T : Towers g.count) (k : ℝ) :=
    H'.metric.acts c * (H'.inverse.acts c - (installed g T.T).transpose * H.inverse.acts f * installed g T.T - k⁻¹ • (Exterior.d 1 c*(Exterior.d 1 c).transpose))*H'.metric.acts c

-- no tableau for a wrong period

def Bleeps (g : Ratio c f) (H H' : Bed) (T : Towers g.count) (k : ℝ) (B : C3) := defect g H H' T k=(Exterior.d 2 c).transpose*B.acts c*Exterior.d 2 c

def Reaches (B : C3) (b : ℝ) : Prop := ∀ p : Momentum, star p=p → IsHermitian (B.read p) ∧ ∀ x : TypeFace 2 → ℂ,
    let v := symbol 2 p*ᵥ x
    b* (dotProduct (star v) v).re ≤ (dotProduct (star v) (B.read p *ᵥ v)).re

def Funds {ι : Type} [Fintype ι] (B : Row ι ι) (v A : ℝ) : Prop := ∀ p : Momentum, star p=p → IsHermitian (B.read p) ∧ ∀ x : ι → ℂ,
    v* (dotProduct (star x) x).re ≤ (dotProduct (star x) (B.read p*ᵥ x)).re ∧
    (dotProduct (star x) (B.read p*ᵥ x)).re ≤ A*(dotProduct (star x) x).re

def Pledge (U V : C3) := ∀ n : Side,(d 2 n).transpose * V.acts n * d 2 n=(d 2 n).transpose * U.acts n * d 2 n

def Opens (Z : C3) (P : C3) := ∀ n : Side, Z.acts n=(P.acts n).transpose * P.acts n

-- physical algebra at ONE ratio + pen κ. `Replaces` demands all n to show uniform.
abbrev bond (H : Bed) (p : Clip) (n : Side) : Matrix (Co n Layers2) (Co n Layers2) ℝ :=
    H.full p n*H.inverse.acts n*(H.full p n).transpose

def stack {α θ β : Type*} {n : Side} (P : Matrix (Co n α) θ ℝ) (Q : Matrix (Co n β) θ ℝ) : Matrix (Co n (α⊕β)) θ ℝ :=
    of fun i j => i.2.elim (fun x => P (i.1,x) j) (fun y => Q (i.1,y) j)

structure Replaces (g : Ratio c f) (H H' : Bed) (p p' : Clip) (k : ℝ) (A : C3) (S T : Towers g.count) : Prop where
  first : S.A0=T.A0
  form : S.T=T.T
  mf : installed g T.mf=H.full p f*H.inverse.acts f*installed g S.T*(H'.full p' c).transpose
  mn : T.mn.acts c=(Real.sqrt k)⁻¹ • ((d 1 c).transpose*(H'.full p' c).transpose)
  image : T.o.acts c=stack (1-bond H' p' c) (A.acts c * d 2 c * H'.inverse.acts c * (H'.full p' c).transpose)

/-- supplied by RAW cumulative kernels + C_3 factor before repair
        (red RHorizon0). Powers & costs depend neighbor dynamics; real spectrum
        reaches ALL at grid. Allow narrower clip selected earlier. -/
structure Rack {G : Gauge} (a : Levels G) (X : MapPrices) (B : Horizon a) : Prop where
  covers N i : i ≤ N → (B.H N i).covered (X.α (a.clock.J i)) (X.Ω (a.clock.J i))
  traces N i : i ≤ N → ∀ n,Floor (B.H N i) (a.params i).clip n (X.η (a.clock.J i)) (X.Ω (a.clock.J i))
  oath N i n : i ≤ N → Bid.Sworn (B.H N i) n G
  top N n : (B.H N N).diagonal.acts n=1
  legs N i : i < N → Donate (B.towers N i) (X.α (a.clock.J (i+1))) (X.Ω (a.clock.J (i+1))) (a.clock.J (i+1)-2)
  crosses N i p : i<N → Towers.Diagonal (a.clock.op i p) (B.H N (i+1)) (B.H N i) (B.towers N i)
  creak N i : i < N →
    let j:= a.clock.J (i+1)
    ∃ P : C3, P.strip (X.α j) (X.Ω j) ∧ Reaches P (X.η j) ∧ ∀ p,
      Bleeps (a.clock.op i p).ratio (B.H N (i+1)) (B.H N i) (B.towers N i) a.clock.kernel.penalty P

end YM.Craft

namespace YM.Bid
open Filter Function Lattice RG Wilson Precision Tree Exterior Bloch Laurent Pressure
open Craft
open Matrix (IsHermitian transpose)
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators NNReal InnerProductSpace

/-- enlarge positive margin from *every* subrange (3-form), pre-L. -/
def F06 : Prop := ∀ (A v η : ℝ), 0 < v → 0 < η → ∃ w B e : ℝ, 0<w ∧ 0 < e ∧ ∀ Q : C3, Reaches Q v → Q.strip η A →
    ∃ P : C3, Funds P w B ∧ P.strip e B ∧ Pledge Q P

def SqActs {ι : Type} [Fintype ι] (Q P : Row ι ι) :=
    ∀ n : Side, Q.acts n=(P.acts n).transpose * P.acts n ∧ Matrix.IsSymm (P.acts n)

def F07 : Prop := ∀ (ι : Type) [Fintype ι] (A v η : ℝ), 0 < v → 0 < η → ∃ w B e : ℝ, 0<w ∧ 0 < e ∧ ∀ Q : Row ι ι,
    Q.strip η A → Funds Q v A → ∃ P : Row ι ι, Funds P w B ∧ P.strip e B ∧ SqActs Q P

def F08 : Prop := ∀ (p q : Clip) (K Ω σ σ' Ω' ν V : ℝ) (X : ℕ), 0 < K → 0<σ → 0<σ' → 0<ν → ∃ γ M : ℝ, 0<γ ∧
    ∀ H H' : Bed,H.covered σ Ω → H'.covered σ' Ω' → ∀ P : C3,P.strip ν V →
      ∀ L : Side,Odd L.val → ∀ S : Towers L, Donate S σ Ω X → ∃ T : Towers L,
        T.Deep γ M X ∧ ∀ (c f : Side) h, Replaces (Ratio.mk (c:=c) (f:=f) L h) H H' p q K P S T

/-- algebra identification, no C3 kernel theory. -/
def F09 : Prop := ∀ (c f : Side) (S : StepData c f) (A B : Towers S.patch.L) (H H' : Bed) (P C : C3) (p q : Clip) (x y v w : ℝ),
    Replaces S.ratio H H' p q S.kernel.penalty P A B → Floor H p f x y → Floor H' q c v w →
    Towers.Diagonal S H H' A → Opens C P → Bleeps S.ratio H H' A S.kernel.penalty C → Towers.Roll S H H' B p q

-- stage alpha dependence bookkeeping (post FaceCoal) for integration. No Alpha repair of Path weights here.
def Retained {G : Gauge} {A : Levels G} (M H : Horizon A) := M.H=H.H ∧ ∀ N m : ℕ,m<N →
      (M.towers N m).A0=(H.towers N m).A0 ∧ (M.towers N m).T=(H.towers N m).T

theorem pinning (a : F06) (b : F07) (c : F08) (d : F09) {G : Gauge} (P : Supply.Sheet G) (Q : MapPrices) :
    ∃ K : MapPrices, ∀ A : Levels G,A.clock.stage=P.profile → A.clock.kernel=P.kernel →
      ∀ B : Horizon A, Rack A Q B → ∃ T : Horizon A, Retained T B ∧ T.Suffices K := by
  classical
  choose w e v hw hv H using fun i : ℕ => a (Q.Ω i) (Q.η i) (Q.α i) (Q.eta_pos i) (Q.alpha_pos i)
  choose y X z hy hz H' using fun i : ℕ => b (TypeFace 3) (e i) (w i) (v i) (hw i) (hv i)
  choose t u ht I using fun i j : ℕ => c (P.profile j).clip (P.profile i).clip P.kernel.penalty (Q.Ω j) (Q.α j) (Q.α i)
    (Q.Ω i) (z j) (X j) (j-2) P.kernel.penalty_pos (Q.alpha_pos j) (Q.alpha_pos i) (hz j)
  let K : MapPrices := { Q with
    α := fun j => min (Q.α j) (min (t j j) (t (j-1) j))
    Ω := fun j => max (Q.Ω j) (max (u j j) (u (j-1) j))
    alpha_pos := fun j => lt_min (Q.alpha_pos j) (lt_min (ht j j) (ht _ _)) }
  refine ⟨K,fun A he hb B R => ?_⟩
  have hm (N i : ℕ) : ∃ T : Towers (A.S.block i), i < N →
      let S := B.towers N i; let j := A.clock.J (i+1); let W := B.H N (i+1); let Y := B.H N i
      T.Deep (K.α j) (K.Ω j) (j-2) ∧ T.A0=S.A0 ∧ T.T=S.T ∧ ∀ p : ℕ,
        Towers.Diagonal (A.clock.op i p) W Y T ∧ Towers.Roll (A.clock.op i p) W Y T (A.params (i+1)).clip (A.params i).clip := by
    by_cases Hn : i<N
    · let j := A.clock.J (i+1)
      let k := A.clock.J i
      have hk : k=j ∨ k=j-1 := by
        have hx : k ≤ j := A.fits.mono (Nat.le_succ i)
        have hh : j ≤ k+1 := A.fits.stepSlow i
        omega
      have hs : (A.params i).clip = (P.profile k).clip := by unfold Levels.params Calendar.params; rw [he]
      have ha : (A.params (i+1)).clip = (P.profile j).clip := by unfold Levels.params Calendar.params; rw [he]
      obtain ⟨Y,hY,g1,g2⟩ := R.creak N i Hn
      obtain ⟨M,hr,hM,hQ⟩ := H _ Y g1 hY
      obtain ⟨M',hn,hM',hSq⟩ := H' _ M hM hr
      let l := A.S.block i
      obtain ⟨T,hF,hT⟩ := I k j (B.H N (i+1)) (B.H N i) (R.covers _ _ Hn) (R.covers _ _ Hn.le)
        _ hM' l (A.S.block_odd i) _ (R.legs N i Hn)
      have hh (p : ℕ) : Replaces (A.clock.op i p).ratio (B.H N (i+1)) (B.H N i) (A.params (i+1)).clip (A.params i).clip
          (A.clock.op i p).kernel.penalty M' (B.towers N i) T := by rw [hs,ha,show (A.clock.op i p).kernel=P.kernel from hb]; exact hT _ _ _
      refine ⟨T,fun _ => ?_⟩
      refine ⟨?_, (hh 0).first.symm, (hh 0).form.symm, fun p => ⟨?_, d _ _ _ _ _ _ _ M' M _ _ _ _ _ _ (hh p) (R.traces _ _ Hn _) (R.traces _ _ Hn.le _) (R.crosses _ _ _ Hn) (fun n => (hSq n).1) ?_⟩⟩
      · have hα : K.α j ≤ t k j := le_trans (min_le_right ..) (hk.elim (fun he => by rw [he]; exact min_le_left ..) (fun he => by rw [he]; exact min_le_right ..))
        have hΩ : u k j ≤ K.Ω j := le_max_of_le_right (hk.elim (fun he => by rw [he]; exact le_max_left ..) (fun he => by rw [he]; exact le_max_right ..))
        obtain ⟨u1,u2,u3,u4⟩ := hF
        exact ⟨fun i j => (u1 i j).mono hα hΩ, fun i j => (u2 i j).mono hα hΩ,fun i j => (u3 i j).mono hα (div_le_div_of_nonneg_right hΩ (by positivity)),fun a hh => ⟨fun i j => ((u4 a hh).1 i j).mono hα (div_le_div_of_nonneg_right hΩ (by positivity)),fun i j => ((u4 a hh).2 i j).mono hα (div_le_div_of_nonneg_right hΩ (by positivity))⟩⟩
      · obtain ⟨h1,h2,h3⟩ := R.crosses N i p Hn
        constructor
        · rw [show T.A0=_ from (hh p).first.symm]; exact h1
        · rw [show T.T=_ from (hh p).form.symm]; exact h2
        rw [show T.A0=_ from (hh p).first.symm, show T.T=_ from (hh p).form.symm]; exact h3
      exact (g2 p).trans (hQ _).symm
    exact ⟨B.towers N i,fun H => False.elim (Hn H)⟩
  choose t hT using hm
  let T := { B with towers := t }
  refine ⟨T,⟨rfl,fun N i ha => ⟨(hT _ _ ha).2.1,(hT _ _ ha).2.2.1⟩⟩,?_⟩
  refine ⟨fun N i hi => ?_, fun N i hi n => ?_,fun N i hi => (hT N i hi).1,fun N i p hi => ((hT N i hi).2.2.2 p).1,
    fun N i p hi => ((hT N i hi).2.2.2 p).2, R.top⟩
  · obtain ⟨h1,h2,h3,h4,h5⟩ := R.covers N i hi
    exact ⟨fun x y => (h1 x y).mono (min_le_left ..) (le_max_left ..),fun x y => (h2 x y).mono (min_le_left ..) (le_max_left ..),fun x y => (h3 x y).mono (min_le_left ..) (le_max_left ..),fun x y => (h4 x y).mono (min_le_left ..) (le_max_left ..),fun x y => (h5 x y).mono (min_le_left ..) (le_max_left ..)⟩
  have hp := R.traces N i hi n
  refine { hp with uniform := ⟨fun x => ?_,fun x => ?_⟩ }
  · have hΩ := hp.uniform.1 x
    exact ⟨hΩ.1,hΩ.2.trans (mul_le_mul_of_nonneg_right (le_max_left ..) (by unfold dotProduct; apply Finset.sum_nonneg; intro i _; rw [← sq]; positivity))⟩
  have hΩ := hp.uniform.2 x
  exact ⟨hΩ.1,hΩ.2.trans (mul_le_mul_of_nonneg_right (le_max_left ..) (by unfold dotProduct; apply Finset.sum_nonneg; intro i _; rw [← sq]; positivity))⟩
end YM.Bid
