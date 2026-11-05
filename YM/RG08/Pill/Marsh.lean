import YM.RG08.Pill.Facing
/-!
# Triangular product bill in common coupling (same d). Substitution preserves.
No universal-g estimate from a neighborhood of the real trajectory. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Pill
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Matrix Summit PertExtension.Series.Tested PertExtension.Series.Radial Scores PowerSeries Door
open scoped BigOperators Topology Real ContDiff
variable {X:Chain}{G:Gauge}{E e N r d τ D j t i k m l n s :ℕ}{R θ C w:ℝ}{F:Labels.Frame G d}{Ω:SectionData F}{ν:G.ColorIndex}{D':ChartRatio G}{H:Hol G}{P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}
variable {h:1/2≤R}{hD:d+1≤D} {T:Signals P Q E τ H Ω h hD}
open Wings Summit
local notation "⨯" => (PowerSeries.X:PowerSeries ℝ)
local notation "Z" => ladder X ν D' N

section loop
open DeckSeat
variable {I:Type}{a b:I→ℕ→ℝ}{L:I→ℕ}{y δ:I→ℝ}
private lemma walked {f g:I→ ℕ→ℝ} (he: Audience y)(hp:0≤δ)(ht:Weighed y (fun i=> (L i:ℝ)))(hx: Dig y δ (fun i=> f i 0))(hh:Dig (fun i:DeckSeat L 1=> y i.i) (fun i=>δ i.i) (fun i=>g i.i i.k))(hg: ∀ i k,k < L i→ ‖f i (k+1)‖ ≤ ‖f i k‖+‖g i k‖) : Dig (fun i:DeckSeat L 0=>y i.i) (fun i=>δ i.i) (fun i=> f i.i i.k) := by
  obtain ⟨A,hA,hx⟩:=hx.asset; obtain ⟨B,⟨C,r,hC,hZ⟩,hh⟩:=hh.asset
  refine ⟨_,(hA.plus (ht.times ((Weighed.constant y hC).times (Weighed.power y he r))) he).transfer i,fun t=>?_⟩
  let b := t.i; let U k:= (A b+(k:ℕ)*(C*y b^r))*δ b
  have hz k (hk:k ≤ L b): ‖f b k‖≤ U k:= by
    induction k with
    | zero=> simpa only [U, Nat.cast_zero,zero_mul,add_zero] using hx b
    | succ k ih=>
      have ht: k < L b:= hk
      apply (hg b k ht).trans; have hp' := hp b
      have hP := hh ⟨b,k,ht⟩; refine ((add_le_add (ih ht.le) (hP.trans (mul_le_mul_of_nonneg_right (hZ _|>.2) hp')))).trans_eq ?_; change U k+C*y b^r*δ b=U k.succ; unfold U; push_cast; ring
  have hY: t.k≤ L b:= t.hw; apply (hz _ hY).trans; have hP:0≤δ b:=hp b; have hh:0≤y b:= (he b).trans' zero_le_one; change U _ ≤ (A b+(L b:ℝ)*(C*y b^r))*δ b; unfold U; gcongr
lemma sofa (f:I→ℕ→ℝ)(h : Audience y)(hl:Weighed y (fun i=> (L i:ℝ))) {g W Q:I→ℕ→ℝ}(hb : 0≤δ)(hc: Lease y δ (fun i=> f i 0) (fun i=>g i 0))(hm:Lease (fun i:DeckSeat L 1=> y i.i) (fun i=>δ i.i) (fun i=> W i.i i.k) (fun i=>Q i.i i.k))
    (he:∀ i k,k<L i→ ∃ p:ℝ, ‖p‖≤1 ∧ f i (k+1)=p*f i k+ W i k ∧ g i (k+1)=p*g i k + Q i k): Lease (fun i:DeckSeat L 0=>y i.i) (fun i=>δ i.i) (fun i=>f i.i i.k) (fun i=> g i.i i.k) := by
    have hx : 0≤ (1:I→ℝ):= fun _=> zero_le_one
    have hu(v p w:ℝ)(hp:‖p‖≤1): ‖p*v+w‖ ≤ ‖v‖+‖w‖:= (norm_add_le ..).trans (add_le_add (by rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) hp) le_rfl)
    constructor
    · exact (walked (δ:=1) h hx hl (Dig.of_rate hc.1) (Dig.of_rate hm.1) (fun i k hk=> by obtain ⟨p,hP,H,H'⟩:=he i k hk; rw [H]; exact hu _ _ _ hP)).rates
    · exact (walked (δ:=1) h hx hl (Dig.of_rate hc.2) (Dig.of_rate hm.2) (fun i k hk=> by obtain ⟨p,hP,H,H'⟩:=he i k hk; rw [H']; exact hu _ _ _ hP)).rates
    refine (walked (f:=fun i k=> f i k-g i k) (g:=fun i k=>W i k-Q i k) h hb hl (Dig.of_lease hc) (Dig.of_lease hm) ?_).asset
    intro i k hk; obtain ⟨p,hP,H,H'⟩:= he i k hk
    rw [H,H',show p*f i k+ _-_= p*(f i k-g i k)+(W i k-Q i k) by ring]; exact hu _ _ _ hP
variable {M T:I→ℕ→ Session (Letter F)}
def turn (S:ℕ→ Session (Letter F)) (n:ℕ) : Session (Letter F):= match n with | 0=>1| n+1=> S n*turn S n
def Thick (L : Side)(A:Session (Letter F)): Prop := (∀ b v:Letter F,b ≠ v → hot A 0 b v≠0 → casc v < casc b) ∧ ∀ b:Letter F, hot A 0 b b=((L.val:ℝ)^(d-fee b))⁻¹
private def payW (M X:Session (Letter F)) (n:ℕ)(b a:Letter F):= ∑ i∈wheel n,∑ p:Letter F,if i.1=0 ∧ b=p then 0 else hot M i.1 b p * hot X i.2 p a
lemma combines (S:ℕ→Session (Letter F))(b v:Letter F) : hot (turn S (n+1)) k b v= hot (S n) 0 b b*hot (turn S n) k b v+payW (S n) (turn S n) k b v:= by
   let W i s:= hot (S n) i b s
   let V i s:= hot (turn S n) i s v
   let s:= wheel k
   let R (i:ℕ×ℕ) j:= W i.1 j* V i.2 j
   let D (i:ℕ×ℕ):=∑ j:Letter F,R i j; let Q (i:ℕ×ℕ):= ∑ j:Letter F, (if i.1=0∧ b=j then 0 else R i j)
   have hz : ∀ i∈ s,D i= (if i=(0,k) then W 0 b*V k b else 0)+ Q i := by
     intro i hi; split; next hp=>
        subst i; unfold D Q
        rw [← Finset.add_sum_erase _ _ (mem_univ b),← Finset.add_sum_erase _ (fun j:Letter F=>if (0,k).1=(0:ℕ) ∧ b=j then 0 else R (0,k) _) (mem_univ b),if_pos ⟨rfl,rfl⟩,zero_add]; change R (0,k) b+_= R (0,k) b+_; congr 1; refine sum_congr rfl fun j hj=> ?_; rw [if_neg (by have hx:= mem_erase.mp hj; tauto)]
     next hp=> rw [zero_add]; refine sum_congr rfl fun j hj=>?_ ; rw [if_neg (by cases i; simp only [Prod.mk.injEq] at hp; have hx:= mem_antidiagonal.mp hi; omega)]
   rw [turn,hot_mul,Matrix.sum_apply]; simp_rw [Matrix.mul_apply]; change ∑ i∈s,D i= W _ _ * V _ _ + ∑ i∈s,Q i; rw [Finset.sum_congr rfl hz,sum_add_distrib]; simp [s,wheel]

lemma ticker (h:Audience y)(he:0≤δ)(hp:Weighed y (fun i=> (L i:ℝ))) (f: I→ℕ→Side) (hx : ∀ i k,k<L i→ Thick (f i k) (M i k)) (hv : ∀ i k,k<L i→ Thick (f i k) (T i k)) (hf:∀ i≤ n,Lying (fun i:DeckSeat L 1=> y i.i) (fun i=> δ i.i) (fun j=> hot (M j.i j.k) i) (fun j=> hot (T j.i j.k) i)) : Lying (fun i:DeckSeat L 0=>y i.i) (fun i=>δ i.i) (fun j=>hot (turn (M j.i) j.k) n) (fun j=> hot (turn (T j.i) j.k) n) := by
   induction n using Nat.strong_induction_on with
   | h n ih=>
    intro b a; generalize hz : casc b=k
    induction k using Nat.strong_induction_on generalizing b with
    | h k IH=>
      let P i j := M i j; let F i j:=T i j
      refine sofa (g:=fun i j=> hot (turn (T i) j) n b a) (L:=L) (fun i j=> hot (turn (M i) j) n b a) h hp (W:=fun i j=>payW (P i j) (turn (M i) j) n b a) (Q:=fun i j=>payW (F i j) (turn (T i) j) n b a) he ?_ ?_ ?_
      · simp only [turn]; exact Lease.const ..
      · unfold payW; refine Lease.lists _ _ (fun i=> h _) fun j hj=> Lease.lists _ _ (fun i=> h _) fun p _=> ?_
        have ht:= mem_antidiagonal.mp hj
        split; exact Lease.const ..; next hn=>
          by_cases hQ:j.1=0
          · by_cases hP:casc p<casc b
            · refine Lease.times (hf j.1 (by omega) b p) ?_ (fun i=> h _)
              rw [show j.2=n by omega]; exact Summit.Lease.whirls (IH (casc p) (by omega) p rfl) down -- t arg
            have he(i:DeckSeat L 1):hot (P i.i i.k) j.1 b p=0:=hQ.symm ▸ not_ne_iff.mp (fun hg=> hP ((hx _ _ i.hw).1 b p (fun H=> hn ⟨hQ,H⟩) hg))
            have hh(i:DeckSeat L 1):hot (F i.i i.k) j.1 b p=0:=hQ.symm ▸ not_ne_iff.mp (fun hg=> hP ((hv _ _ i.hw).1 b p (fun H=> hn ⟨hQ,H⟩) hg))
            simp_rw [he,hh,zero_mul]; exact Lease.const ..
          exact Lease.times (hf _ (by omega) b p) (Summit.Lease.whirls (ih j.2 (by omega) (fun i hi=> hf i (by omega)) p a) down) (fun i=> h _)
      intro i j hj; have hM: hot (M i j) 0 b b= _:= (hx i j hj).2 b
      refine ⟨hot (M i j) 0 b b,?_,combines ..,?_⟩
      · rw [(hx _ _ hj).2]; let t : Side:= f i j; have hp : 1≤ (t.val:ℝ)^(d-fee b):= one_le_pow₀ (by exact_mod_cast t.property); rw [Real.norm_of_nonneg (by positivity)]; exact inv_le_one_of_one_le₀ hp
      · exact (combines ..).trans (by rw [(hv _ _ hj).2,(hx _ _ hj).2])
end loop
end YM.RG08.Pill
