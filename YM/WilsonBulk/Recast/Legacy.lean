import YM.WilsonBulk.Recast.Quotes

/-! # Prefix normalization cost for producing independently specified running-coefficient. Formal algebra. Includes actual RG color readout χ, not merely θ= projection post chosen. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
namespace Recall
open PowerSeries Filter Function Finset Sheet Album
open scoped Topology BigOperators Classical
variable {A B : Type} {x y p q r s δ : ℝ} {n k e : ℕ} {u v z u' v' : Word}
variable {f g t : ℝ→ℝ} {H G : Word→Word}

def inverseCost (n : ℕ) (p : ℝ) := ∑ i∈range n, port n (1+p) i
lemma tariff_inv (n : ℕ) (h : Tariff f) : Tariff fun x=>inverseCost n (f x) := Tariff.gather _ fun _ _=> orbit_tariff n _ ((Tariff.const 1 zero_le_one).add h)
lemma inversionSteps (n : ℕ) {A : Type} [CommRing A] (p : PowerSeries A) (hp : constantCoeff p=1) : Steps n (∑ i∈range n,(1-p)^i) (recover p) := by
  let S:= ∑ i∈range n,(1-p)^i; let H:=S*p
  have hh : Steps n ((1-p)^n) 0 := Steps.dvd.mpr (by rw [sub_zero]; exact pow_dvd_pow_of_dvd (X_dvd_iff.mpr (by rw [map_sub,hp,map_one,sub_self])) n)
  have hx : Steps n H 1:= by rw [show H=1-(1-p)^n from by unfold H S; simpa using _root_.geom_sum_mul_neg (1-p) n]; convert minus_clock (p:=1) Steps.self hh using 1; simp
  rw [show (∑ i∈range n,(1-p)^i)=H*recover p from by unfold H; rw [mul_assoc,mul_comm p, rec_one hp,mul_one]]; exact Steps.trans (Steps.mul hx Steps.self) (by rw [one_mul]; exact Steps.self)
lemma albumInverse (h : Album n δ p u v) (hp : constantCoeff u=1) (hv : constantCoeff v=1) : Album n δ (inverseCost n p) (recover u) (recover v) := (Album.sum (range n) _ _ _ h.radiusM (fun i _=> ((Album.one n h.radiusM).sub h).powers i)).reform (inversionSteps n _ hp) (inversionSteps n _ hv)

def verdict (n : ℕ) (p q : ℝ) := 1+ |(1/2:ℝ)| * (p+1+port n (q+1) 2)
lemma verdict_cash (n : ℕ) (h : Tariff f) (hp : Tariff g) : Tariff (fun x=> verdict n (f x) (g x)) := (Tariff.const 1 zero_le_one).add ((Tariff.const _ (abs_nonneg _)).prod ((h.add (Tariff.const 1 zero_le_one)).add (orbit_tariff n _ (hp.add (Tariff.const 1 zero_le_one)))))
lemma judge (h : Album n δ q u v) (he : Album n δ p (H u) (G v)) : Album n δ (verdict n p q) (decision H u) (decision G v) := (Album.one n h.radiusM).plus ((((he.sub (Album.one n h.radiusM)).sub ((h.sub (Album.one n h.radiusM)).powers 2)).scale _)) -- parentheses
-- clock iteration owns mechanism. polynomial quoted at n steps.

def wages (n : ℕ) (F : ℝ→ℝ→ℝ) (p : ℝ) : ℕ→ℝ
| 0=>1
| i+1=> F p (wages n F p i)
lemma wages_tag (Q : ℝ→ℝ→ℝ) (p : ℝ→ℝ) (n i : ℕ) (h : Tariff p) (he : ∀ {p v}, Tariff p → Tariff v → Tariff fun x=> Q (p x) (v x)) : Tariff fun x=>wages n Q (p x) i := by
  induction i with
  | zero=> exact Tariff.const 1 zero_le_one
  | succ i ih=> exact he h ih -- defeq?
lemma albumSaga (F : ℝ→ℝ→ℝ) (p : ℝ) (hh : ∀ {x y q}, Album n δ q x y → Album n δ (F p q) (H x) (G y)) (hv : Poised H) (hp : Poised G) (he : 0≤δ) : Album n δ (wages n F p n) (saga H) (saga G) := by
  have ht k : Album n δ (wages n F p k) (H^[k] 1) (G^[k] 1):= by
    induction k with
    | zero=> exact Album.one _ he
    | succ k ih=> rw [wages,Function.iterate_succ_apply',Function.iterate_succ_apply']; exact hh ih
  exact (ht n).reform (hv.seasons n).symm (hp.seasons n).symm

def pollCost (n : ℕ) (p : ℝ) := wages n (fun x y => verdict n (tabBar n y x) y) p n
def moonCost (n : ℕ) (p : ℝ) := wages n (verdict n) p n
def yesterCost (n : ℕ) (p : ℝ) := inverseCost n (moonCost n p)
lemma tariff_poller (n : ℕ) (hp : Tariff f) : Tariff (fun x=> pollCost n (f x)) := wages_tag _ _ _ _ hp (fun h hv=> verdict_cash n (bar_tag hv h) hv)
lemma tariff_moon (n : ℕ) (hp : Tariff f) : Tariff (fun x=> moonCost n (f x)):= wages_tag _ _ _ _ hp (fun h hv=> verdict_cash n h hv)
lemma tariff_yesterday (n : ℕ) (hp : Tariff f) : Tariff (fun x=> yesterCost n (f x)):= tariff_inv _ (tariff_moon n hp)

lemma pollAlbum (p : ℝ) (he : Album n δ p u v) (hp : constantCoeff u=1) (hv : constantCoeff v=1) : Album n δ (pollCost n p) (polling u) (polling v) := albumSaga (n:=n) _ p (H:=_) (fun hx=> judge hx (albumBar hx he)) (poll_safe hp) (poll_safe hv) he.radiusM
lemma yestAlbum (p : ℝ) (he : Album n δ p u v) (hp : constantCoeff u=1) (hv : constantCoeff v=1) : Album n δ (yesterCost n p) (yesterday u) (yesterday v) := albumInverse (albumSaga (n:=n) _ p (H:=_) (fun hx=> judge hx he) (arise_safely hp) (arise_safely hv) he.radiusM) (arises_rule hp).1 (arises_rule hv).1
end Recall
namespace Parapet
open PowerSeries Filter Function Finset Sheet Recall Album Atelier
open scoped Topology BigOperators Classical
variable {G : Gauge} {V U : Text (Cloth G) 2} {P Q : Library G}
variable {n e : ℕ} {σ A x δ : ℝ}
lemma moment_lip (k : G.ColorIndex) (h : Options (lawn _) σ δ A V U) (hx : Public V) (hy : Public U) (hs : 0<σ) : Reel δ (momentWeight σ 2*A) (subdue k V) (subdue k U) := ⟨subdue_price _ h.plus hs,subdue_price _ h.minus hs,by rw [← subdue_minus hy hx,mul_left_comm]; exact subdue_price k h.variation hs,h.nonneg⟩
lemma moments_book (k : G.ColorIndex) (h : ∀ i:ℕ,i < e→ Options (lawn _) σ δ A (P i 2) (Q i 2)) (hx : Pamphlet P) (hy : Pamphlet Q) (hs : 0<σ) (he : 0≤ A) (hp : 0 ≤ δ) (hv : momentWeight σ 2 ≤ A) : Album e δ (A*A) (revenue k P) (revenue k Q) := by refine ⟨fun i hi=>?_,mul_self_nonneg _,hp⟩; rw [earnings,earnings]; exact (moment_lip k (h i hi) (hx _ _) (hy _ _) hs).more (by gcongr) le_rfl
end Parapet
end YM.WilsonBulk
