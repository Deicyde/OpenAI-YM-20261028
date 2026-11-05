import YM.Pert.Bulk.Inherit

/-! Single common exponential norm on each finite packet demand, no per-step width loss for the indicated pull. Includes exact matrix periodization and Face intertwining explicitly linked to the same horizon/stages. -/
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Bulk
open Lattice Laurent RG Function Precision Filter Bloch Exterior Matrix
open scoped ENNReal Topology Classical BigOperators
variable {α β:Type} {G : Gauge} {a:Levels G} {H : Horizon a} {n:Side} {L : Side}
lemma merit {K : Bed} {σ p:ℝ} (h: K.covered σ p) : 0≤p :=
    let i := plaquette ⟨((0:Axis),(1:Axis)),by decide⟩
    (tsum_nonneg (g:=fun z=>Real.exp (σ * size z) * ‖K.inverse i i z‖) fun x=>(h.2.2.1 i i).1 x).trans (h.2.2.1 i i).2.2

def allotment (P:MapPrices) (j i:ℕ) := pre Faces Faces (P.Ω j) (Real.exp 4 * P.Ω j) (P.Ω i)
def fine_share (H : Horizon a) (N m:ℕ) := response (H.towers N m) (H.H N (m+1)) (H.H N m)
def carrier_share (H : Horizon a) (N m p:ℕ) := carrier (a.clock.op m p).ratio (H.towers N m) (H.H N (m+1)) (H.H N m)
lemma values {P:MapPrices}(h:H.Suffices P) {N m:ℕ}(hk:m<N)(p:ℕ): Matches (fine_share H N m) (carrier_share H N m p) := by
     apply matches_response (u:=_) (a:=P.α (a.clock.J (m+1))) (b:=P.α (a.clock.J m)) (σ:=P.α (a.clock.J (m+1))) (p:=P.Ω (a.clock.J (m+1))) (q:=P.Ω (a.clock.J (m+1))/((a.S.block m).val :ℝ)^2) (g:=(a.clock.op m p).ratio)
     · exact ((h.costs N m hk).2.2.2 [] (Nat.zero_le _)).2
     · exact h.rows N _ hk
     · exact h.rows N _ hk.le
     · exact (P.alpha_pos _).le
     · rfl
     · exact (P.alpha_pos _).le
     · exact merit (h.rows N (m+1) hk)
     exact div_nonneg (merit (h.rows N (m+1) hk)) (by positivity)
lemma birth {P:MapPrices}(h:H.Suffices P) {N m:ℕ}(hk:m<N)(p:ℕ) :
   carrier_share H N m p * d 1 (a.S.side m p) = d 1 (a.S.side (m+1) p) * installed (a.clock.op m p).ratio (H.towers N m).A0 := by
     exact inherited_precision _ _ (h.crossings _ _ _ hk) (h.all _ _ hk _) (h.all _ _ hk.le _)

def palette (P:MapPrices)(j i:ℕ)(r:ℕ):ℝ := min 1 (min (P.α j) (P.α i))/(r+1)
lemma width_le (P:MapPrices) (i j r:ℕ) {σ:ℝ} (hσ:σ≤ palette P i j r) : σ≤ min 1 (min (P.α j) (P.α i)) ∧ r*σ ≤ min 1 (min (P.α i) (P.α j)) := by
     have hbudget : 0≤ min 1 (min (P.α i) (P.α j)) := le_min (by norm_num) (le_min (P.alpha_pos _).le (P.alpha_pos _).le)
     have ht := le_div_iff₀ (show 0<(r+1:ℝ) by positivity) |>.1 hσ
     rw [min_comm (P.α j)]; constructor <;> rcases (show σ≤0 ∨ 0<σ from le_or_gt _ _) with hh|hh
     · exact hh.trans hbudget
     · dsimp [palette] at hσ
       apply hσ.trans
       apply div_le_self
       · exact hbudget
       simp
     · exact (mul_nonpos_of_nonneg_of_nonpos (by positivity) hh).trans hbudget
     nlinarith [Nat.cast_nonneg (α:=ℝ) r]
lemma atlas_here {N m:ℕ} {P:MapPrices}(h:H.Suffices P) (r:ℕ)(hk:m<N):
   Atlas (min 1 (min (P.α (a.clock.J (m+1))) (P.α (a.clock.J m)))) (a.S.block m) 2 (fine_share H N m) (allotment P (a.clock.J (m+1)) (a.clock.J m)) := by
     let i := a.clock.J (m+1); let j:=a.clock.J m
     have hi := merit (h.rows N (m+1) (by omega))
     have hj := merit (h.rows N m (by omega))
     let σ:=min 1 (min (P.α i) (P.α j))
     have hs :0≤ σ := le_min (by norm_num) (le_min (P.alpha_pos _).le (P.alpha_pos _).le)
     have ha : Atlas σ _ .. := priced_atlas (m:=m) h hk (a.S.block_odd m) (Nat.le_trans (by decide : 3≤4) (a.clock.adm _)) hs ((min_le_right ..).trans (min_le_left ..)) ((min_le_right ..).trans (min_le_right ..)) hi hj
     have he : pre Faces Faces (P.Ω i) (Real.exp (4*σ)*P.Ω i) (P.Ω j) ≤ allotment P i j := by unfold allotment pre; gcongr; simp [σ]
     refine ⟨ha.1,ha.2.trans he,fun u v=>(ha.row u v).trans (ENNReal.ofReal_le_ofReal (by gcongr)),fun u v=>(ha.col u v).trans (ENNReal.ofReal_le_ofReal (by gcongr)),fun u => ?_⟩
     intro x v
     exact (ha.step u x v).trans (ENNReal.ofReal_le_ofReal (by gcongr))
set_option maxHeartbeats 600000 in
lemma deep_bound {n:ℕ} (A B c p:ℝ) (hp:0≤p)(hc:0≤c)(ha:0≤A)(hb:0≤B)(h:2≤n) : (B*(c/(L.val:ℝ)^2))^n * (A*(c*(L.val:ℝ)^4/(L.val:ℝ)^2))*p ≤ ((B*c)^n * (A*c)*p)/(L.val:ℝ)^2 := by
  have hu : (1:ℝ) ≤L.val := by exact_mod_cast L.property
  let x : ℝ := L.val
  have hx : 0<x := zero_lt_one.trans_le hu
  have hm : x^4≤ (x^(2*n)) := pow_le_pow_right₀ hu (by omega)
  change (B * (c / x^2))^n * (A*(c*x^4/x^2))*p ≤ _/x^2
  replace hg : c*x^4/x^2 = c*x^2 := by field
  rw [hg, show B*(c/x^2)= (B*c)/x^2 from (mul_div_assoc B c _).symm,div_pow,← pow_mul]
  calc _ = (B*c)^n * (A*c)*p * (x^2/x^(2*n)) := by ring
       _ ≤ _ * ((x^2)⁻¹) := by
                apply mul_le_mul_of_nonneg_left ?_ (by positivity)
                rw [div_le_iff₀ (by positivity)]
                field_simp [hx.ne', (pow_pos hx 2).ne']
                nlinarith [hm]
       _ = _ := rfl

def common (P:MapPrices)(j i r:ℕ) (α:Type) [Fintype α] := (let c:=allotment P j i; ((Fintype.card α*c)^r*(Fintype.card α*c)))
def priced (P:MapPrices)(j i:ℕ)(σ:ℝ)(α:Type)[Fintype α] := (let c:=allotment P j i; (Fintype.card α*(2/σ)*c*(Fintype.card α*c)))
lemma high_receipt {P:MapPrices} (h:H.Suffices P) {N m r:ℕ} {K:Packet r Faces} {σ p:ℝ} (hp:0≤p)(hh:m<N)(hr:2≤r)(hs:0≤σ)(hm:σ≤palette P (a.clock.J (m+1)) (a.clock.J m) r)(ht:Folded σ K p) :
   Folded σ (pull K (fine_share H N m)) ((common P (a.clock.J (m+1)) (a.clock.J m) r Faces)*p/(a.S.block m).val^2) := by
      have hA := atlas_here h r hh
      have hq := width_le _ _ _ _ hm
      have hk := transfer_all hs hA (by rw [min_comm (P.α _) (P.α _)]; exact hq.1) hq.2 ht
      exact fun x=>(hk x).trans (ENNReal.ofReal_le_ofReal (deep_bound _ _ _ _ hp hA.nonneg (by positivity) (by positivity) hr))
lemma square_receipt {P:MapPrices} (h:H.Suffices P) {N m:ℕ}{K:Packet 1 Faces} {σ p:ℝ}(hp:0≤p)(hh:m<N)(hs:0<σ)(hm:σ≤palette P (a.clock.J (m+1)) (a.clock.J m) 1)(ht:Folded σ K p)(hé: neutral K) :
   Folded σ (pull K (fine_share H N m)) ((priced P (a.clock.J (m+1)) (a.clock.J m) σ Faces)*p/(a.S.block m).val) := by
      have hA := atlas_here h 1 hh
      have ⟨_,hq⟩ := width_le _ _ _ _ hm
      exact null_all hs hA (by simpa using hq) ht (by exact_mod_cast (Nat.le_trans (by decide) (a.S.block_large m) : 2≤(a.S.block m).val)) hé
end YM.Pert.Bulk
