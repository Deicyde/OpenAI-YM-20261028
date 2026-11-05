import YM.RG08.Flat.Length

/-!
# No switch of evaluated flat precision is required

Any linear receipt on the actual geometry and penalty uses this same precision (by Schur and
cofinal period tests). No hypothesis whether ITS harmonic predictor branches agree. Thus one can
instantiate the kfalt estimate from the *independent* linear construction without identifying its
off-curl Beds or roll funds with those of the actual receipt.
-/
noncomputable section
namespace YM.RG08.Flat
open Filter Finset Pert.Bulk Laurent Lattice Bloch Stationary Function Matrix RG08.Packets RG08.Rate RG Precision Next.Free Exterior
open scoped Topology ENNReal

set_option autoImplicit false
variable {G : Gauge} {a : Levels G} {H B : Horizon a} {P R : MapPrices}

theorem same_terminal (h:H.Suffices P)(N:ℕ)(c:Side) : quadratic (H.H N N) c=Precision.K 1 := by
  unfold quadratic Precision.K
  rw [Matrix.mul_assoc,(h.all N N le_rfl c).same, h.top N,Matrix.mul_assoc]

theorem same_path (h:H.Suffices P)(ht:B.Suffices R)(N t i:ℕ)(hI:i ≤ N) :
    quadratic (H.H N i) (a.S.side i t)=quadratic (B.H N i) (a.S.side i t) := by
  have he j m (h₁:m ≤ N)(h₂:N=m+j):
      quadratic (H.H N m) (a.S.side m t)=quadratic (B.H N m) (a.S.side m t) := by
    induction j generalizing m with
    | zero => rw [show m=N by omega,same_terminal h,same_terminal ht]
    | succ j hj =>
      have hM : m<N := by omega
      have hP := poised (ht.crossings _ _ t hM).trial (h.crossings _ _ t hM).trial (h.all N (m+1) hM _).symmetric.1 (h.all N m hM.le _).symmetric.1
      apply sub_eq_zero.mp
      apply hP.trans
      have hh : Precision.K ((H.H N (m+1)).metric.acts (a.clock.schedule.side (m+1) t)) = Precision.K ((B.H N (m+1)).metric.acts (a.clock.schedule.side (m+1) t)):= hj (m+1) hM (by omega)
      rw [hh,sub_self,Matrix.mul_zero,Matrix.zero_mul] -- definally quadratic?
  exact he (N-i) i hI (by omega)

theorem same_output (h:H.Suffices P)(ht:B.Suffices R)(N i:ℕ)(hI:i ≤ N):output (H.H N i)=output (B.H N i):= by
  have uses {B:Horizon a}{P}(h:B.Suffices P):
      RowCost 0 1 (output (B.H N i)) (sumToken*(Fintype.card Faces*(P.Ω (a.clock.J i)))) ∧
       ∀ n,Matches (output (B.H N i)) (quadratic (B.H N i) n) :=
    output_cost (fun x y=> ((h.rows N i hI).2.1 x y).mono (P.alpha_pos _).le le_rfl) (Ω_pos h i) le_rfl zero_le_one
  exact readahead (t:=a.S.side i) (mesh_sides a.S i) (uses h).1 (uses ht).1 le_rfl le_rfl (fun t=>(uses h).2 _) (fun t=> same_path h ht N t i hI ▸ (uses ht).2 _)

theorem embedded 
    (h:H.Suffices P) {N i : ℕ} (hi : i<N) (p:ℕ) :
    let S := a.clock.op i p
    let J := H.H N (i+1); let A := H.H N i
    Matches (output J) (quadratic J (a.S.side (i+1) p)) ∧
     Matches (output A) (quadratic A (a.S.side i p)) ∧
     Inputs S (installed S.ratio (H.towers N i).A0) (J.metric.acts (a.S.side (i+1) p)) (A.metric.acts (a.S.side i p)) ∧
     ∀ (F:Tree.Forest S.ratio), let T:=extracted S F (installed S.ratio (H.towers N i).A0)
           let K:=1-probe S*T
           T.transpose*quadratic J (a.S.side (i+1) p)*T+S.kernel.penalty • (K.transpose*K) = quadratic A (a.S.side i p) := by
  intro S J A
  have Hx := (h.crossings _ _ p hi).trial
  have he i (hi:i ≤ N) (p:ℕ) : Matches (output (H.H N i)) (quadratic (H.H N i) (a.S.side i p)) := by
    let j := a.clock.J i
    exact (output_cost (σ:=0) (Y:=H.H N i) (p:=P.Ω j) (fun x y=> ((h.rows N i hi).2.1 x y).mono (P.alpha_pos _).le le_rfl) (Ω_pos h i) le_rfl zero_le_one).2 _
  exact ⟨he _ hi _,he _ hi.le _,Hx,fun F=>Precision.action F _ _ _ Hx⟩
end YM.RG08.Flat
