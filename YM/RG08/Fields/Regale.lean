import YM.RG08.Fields.Frieze

set_option autoImplicit false
noncomputable section
namespace YM.RG08.Drift
open Function Filter Set Lattice Wilson RG Exterior Precision Next.Free
open Laurent Bloch Matrix Work.F08
open scoped Topology BigOperators
variable {j n : ℕ} {k : ℝ}
variable {S : Flight j n}
section
variable {I : Type*} {p : I→Momentum} {u v : I→Train j} {Z : I→ℝ} {σ τ : ℝ}
variable (hk : 0<k) (hn : 4≤n) (hs : 0<σ) (ht : 0<τ) (hZ : ∀ i,0≤Z i) (hp : ∀ i,p i∈baseCube) (he : ∀ i,p i≠0)
    (hf : ∀ i,(minusRows (hessian (pink k (u i))) (hessian (pink k (v i)))).strip σ (Z i))
    (hb : ∀ i,(minusRows (hessian (pink k (flutter S (u i)).land)) (hessian (pink k (flutter S (v i)).land))).strip τ (Z i))
include hk hn hs ht hZ hp he hf hb
lemma decks (l : Site S.L) :
    Beam Z p 12 (fun i=> Flight.pilot k (flutter S (u i)) (p i) l) (fun i=> Flight.pilot k (flutter S (v i)) (p i) l) ∧
    Beam Z p 10 (fun i=> Flight.wire k (flutter S (u i)) (p i) l) (fun i=> Flight.wire k (flutter S (v i)) (p i) l) := by
  let y (l : Site S.L) (i : I):=aliasAt (p i) l
  have hy l i : y l i∈baseCube:= alias_base (hp i) l S.odd
  have hc i := base_subset_realCube zone_pos (hp i)
  have hj l i : y l i≠0 := (alias_regular (P:=S) (hc i) l (Or.inr (he i))).2
  have hi : ∃ L:ℝ,0≤L∧∀ i, rim (p i)≤ L*rim (p i):=⟨1,zero_le_one,fun i => le_of_eq (one_mul _).symm⟩
  have hg (l : Site S.L) : ∃ L:ℝ,0≤L∧∀ i, rim (y l i)≤ L*rim (p i):= ⟨_,(side_pos S.L).le,fun i => rim_alias S.L _ (hp i) (he i)⟩
  let F i:= flutter S (u i); let G i:= flutter S (v i)
  have hm (l : Site S.L) : Wave Z p 2 (fun i=> (F i).total k (y l i)) (fun i=> (G i).total k (y l i)) := Wave.collect hZ (couloir hk S.legal hs hZ (hy l) (hj l) hf (hg l) S.L)
  have hu l := mass_up (w:=p) hZ (hy l) S.patch
  have hY l := ((hu l).1).times ((hu l).2)
  have h0 : Wave Z p 2 (fun i=> (F i).tabE k (p i)) (fun i=> (G i).tabE k (p i)) := Wave.collect hZ (fun i=> (hY i).times (hm i))
  obtain ⟨c,hx,H⟩:=stake_near hk S
  have hw : Wave Z p 2 (fun i=>((F i).tabE k (p i))⁻¹) (fun i=> ((G i).tabE k (p i))⁻¹) := by
    refine h0.invert (b:=0) (fun i=> (F i).tabE_puncture k hk (hc i) (he i)) (fun i=> (G i).tabE_puncture k hk (hc i) (he i)) ⟨c⁻¹,(inv_pos.mpr hx).le,fun i=>?_⟩
    have hh (v): ‖((flutter S v).tabE k (p i))⁻¹‖ ≤ c⁻¹:= by rw [norm_inv]; exact (inv_le_inv₀ (hx.trans_le (H v _ (hp i) (he i))) hx).2 (H v _ (hp i) (he i))
    rw [pow_zero,mul_one]; exact ⟨hh _,hh _⟩
  have hE : Wave Z p 4 (fun i => (F i).weightsE k (p i) (y l i)) (fun i => (G i).weightsE k (p i) (y l i)) := by
    simp only [Flight.weightsE,div_eq_mul_inv]; exact ((((hu l).2).times (hm l)).times hw)
  have hS:= flowP (w:=p) hZ (hy l) S 1
  have hP := glacier_t (w:=p) hk hn ht hZ hp hb
  have hs1 (r : ℕ):= sun (w:=p) hZ hp 1 r
  have hs2 r := sun (w:=p) hZ (hy l) S.L r
  have hB:= fll hk S.legal hs hZ (hy l) (hj l) hf (hg l) S.L
  have hx1:= Beam.times hZ (Beam.times hZ ((hs1 1).2) hP) ((hs1 1).1)
  have hn1 := tides hk hn ht hZ hp he hb hi 1
  have hn2 := tides hk S.legal hs hZ (hy l) (hj l) hf (hg l) S.L
  have hs3 := (Beam.times hZ ((hs1 0).2) (dome (w:=p) hk hn ht hZ hp he hb 1)).scale hn1
  constructor
  · simp_rw [Flight.pilot_match k hk _ (hc _) (he _)]
    apply Beam.plus
    · exact ((Beam.times hZ (Beam.times hZ hB hS) hx1).upright hZ (by omega))
    exact (Beam.times hZ ((hs2 0).1) hs3).scale hE
  simp_rw [Flight.wire_match k hk _ (hc _) (he _)]
  have hC : Wave Z p 8 (fun i=> (F i).chainY k (p i) (y l i)) (fun i=> (G i).chainY k (p i) (y l i)) := by
    simp only [Flight.chainY,div_eq_mul_inv]; exact (((hY l).times (roof (w:=p) hk hn ht hZ hp he hb 1)).times hn2)
  have hv := fll hk hn ht hZ hp he hb hi 1
  have hU := (Beam.times hZ (Beam.times hZ (Beam.times hZ hP ((hs1 1).1)) hv) ((hs1 1).2))
  have hL := glacier_t (w:=p) hk S.legal hs hZ (hy l) hf
  apply Beam.plus
  · exact ((Beam.times hZ (Beam.times hZ (Beam.times hZ (Beam.times hZ hL ((hs2 1).1)) hB) hS) ((hs1 1).2)).upright hZ (by decide))
  exact (Beam.times hZ (flowP (w:=p) hZ (hy l) S 2) (((Beam.home (w:=p) hZ (1:Frequency 2 2)).upright hZ (by decide : 0 ≤ (0+0+2+0))).minus hU)).scale hC

open Flight in
lemma mist :
    (∀ (r : Site S.L), Beam Z p 12 (fun i a b=> ((duo k (flutter S (u i))).A0).read (p i) (r,a) b) (fun i a b=>((duo k (flutter S (v i))).A0).read (p i) (r,a) b)) ∧
    ∀ (r : Site S.L),Beam Z p 12 (fun i a b=> ((duo k (flutter S (u i))).T).read (p i) (r,a) b) (fun i a b=> ((duo k (flutter S (v i))).T).read (p i) (r,a) b) := by
  have hQ:=secure_both k hk S.legal hn
  have h l:= decks hk hn hs ht hZ hp he hf hb l
  let F i:= flutter S (u i); let G i:= flutter S (v i)
  have hx (l : Site S.L) (q : Cover) : Wave Z p 0 (fun i=> mode (aliasAt (p i) l) q) (fun i=> mode (aliasAt (p i) l) q) := Wave.same hZ 1 zero_le_one
    (fun i=> le_of_eq (mode_real _ _ (alias_real (hp i).1 _)))
  have he {α β:Type} {f : Thread j n α β} (g : Secured f) (e : ℕ) (r : Site S.L)
      (hz : ∀ l : Site S.L,Beam Z p 12 (fun i => f (F i) (p i) l) (fun i=> f (G i) (p i) l)) (a : α) (b : β) :
      Wave Z p 12 (fun i=> (meshBook f e [] (F i)).read (p i) (r,a) b) (fun i=> (meshBook f e [] (G i)).read (p i) (r,a) b) := by
    simp_rw [g.bankRead (u:=[]) S.legal e (Nat.zero_le _) _ _ (hp _),spread,Matrix.sum_apply]
    simp only [Matrix.smul_apply,listChip,List.map_nil,List.prod_nil,mul_one,smul_eq_mul]
    have hu:= Wave.collect hZ fun i : Site S.L=> (hx i (lift r)).times ((Wave.constant hZ (toll S.L e)).times (hz i a b))
    exact hu
  exact ⟨fun r i j=> he hQ.1 1 r (fun l => (h l).1) i j,fun r i j=> he hQ.2 2 r (fun l=> ((h l).2).upright hZ (by decide)) i j⟩
end

private structure Book (S : Flight j n) (k σ τ : ℝ) where
  X : ℝ
  p : Momentum
  u : Train j
  v : Train j
  hz : 0≤X
  hp : p∈baseCube
  he : p≠0
  startH : (minusRows (hessian (pink k u)) (hessian (pink k v))).strip σ X
  stepB : (minusRows (hessian (pink k (flutter S u).land)) (hessian (pink k (flutter S v).land))).strip τ X
lemma gearing {σ τ : ℝ} (S : Flight j n) (hk : 0<k) (hn : 4 ≤ n) (hs : 0<σ) (ht : 0<τ) : ∃ C : ℝ, 0<C ∧
    ∀ (u v : Train j) (X : ℝ), 0≤X → (minusRows (hessian (pink k u)) (hessian (pink k v))).strip σ X →
      (minusRows (hessian (pink k (flutter S u).land)) (hessian (pink k (flutter S v).land))).strip τ X → ∀ p∈baseCube, p≠0 →
        let A:=Flight.duo k (flutter S u); let B:=Flight.duo k (flutter S v)
        (∀ i l, ‖(A.A0.read p i l)-(B.A0.read p i l)‖ ≤ C*X*rim p^12) ∧
          (∀ i l, ‖A.T.read p i l-B.T.read p i l‖ ≤ C*X*rim p^12) := by
  let I := Book S k σ τ
  let F (i : I):=Flight.duo k (flutter S i.u); let G (i : I):=Flight.duo k (flutter S i.v)
  let P (i : I):= i.p
  let Z (i : I):= i.X
  have h:= mist (I:=I) (p:=P) (v:=fun i=>i.v) hk hn hs ht (hZ:=fun i=> i.hz) (fun i=> i.hp) (fun i=> i.he) (hf:=fun i=> i.startH) (hb:=fun i=> i.stepB)
  have hF : Beam (ι:=Co S.L (TypeFace 1)) (Ω:=TypeFace 1) Z P 12 (fun i=> (F i).A0.read i.p) (fun i=> (G i).A0.read i.p) := fun ⟨r,a⟩ b => h.1 r a b
  have hC : Beam (ι:=Co S.L (TypeFace 2)) (Ω:=TypeFace 2) Z P 12 (fun i=> (F i).T.read i.p) (fun i=> (G i).T.read i.p) := fun ⟨r,a⟩ b => h.2 r a b
  obtain ⟨c,hc,H⟩ := hF.circum (fun i=> i.hz); obtain ⟨d,hd,U⟩:= hC.circum (fun i=> i.hz)
  refine ⟨c+d+1,by positivity,fun u v X hX ho hY p hp he=>?_⟩
  let i : I:=⟨X,p,u,v,hX,hp,he,ho,hY⟩; intro A B
  have he (a : ℝ) (hh:a≤c+d+1) : a*rim (P i)^12*Z i ≤ (c+d+1)*X*rim p^12:= by
    have hx := rim_live p; change a*rim p^12*X≤_; rw [mul_right_comm]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh hX) (pow_nonneg hx.le _)
  exact ⟨fun x y=> (H x y i).both.trans (he _ (by linarith)),fun x y=> (U x y i).both.trans (he _ (by linarith))⟩
end YM.RG08.Drift
