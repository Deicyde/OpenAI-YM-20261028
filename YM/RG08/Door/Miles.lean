import YM.RG08.Door.Chants
/-!
# One-mark canonical paid signatures incl constant-slot and whole inverse. UV overlap
for actual-circuit approved demands, not volume real cut estimates.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Door
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Matrix
open scoped BigOperators Topology Real
variable {X:Chain}{G:Gauge}{E e r d τ D j t i k m l n s :ℕ}{R θ C w:ℝ}{F:Labels.Frame G d}{Ω:SectionData F}{ν:G.ColorIndex}{D':ChartRatio G}{H:Hol G}{P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}
variable {h:1/2≤R}{hD:d+1≤D} {T:Signals P Q E τ H Ω h hD}
open Wings
variable {I:Type}{u:I→Windows}
section
variable {y δ:I→ℝ}{L : I→Side} {X Y:I→Session (Letter F)}{M A B N:I→Loft F}
def Lying (y δ:I→ℝ)(M N: I→ Loft F) := ∀ i j, Lease y δ (fun a=> M a i j) (fun a=> N a i j)
lemma Lying.plus (hp:Audience y)(h : Lying y δ M N)(he:Lying y δ A B): Lying y δ (M+A) (N+B) := fun i j=> by simpa only [Pi.add_apply, Matrix.add_apply] using! (h i j).plus (he i j) hp
lemma Lying.fixed (hp:Audience y) (U : Loft F) : Lying y δ (fun _=> U) (fun _=> U) := fun _ _=> Lease.const ..
lemma Lying.neg (hp:Audience y)(h: Lying y δ M N) : Lying y δ (-M) (-N) := by
  intro i j; have he:= (h i j).times (Lease.const y δ (-1)) hp; convert he using 1 <;> funext i <;> simp
lemma Lying.times (hp : Audience y)(h:Lying y δ M N)(he:Lying y δ A B) : Lying y δ (fun i=>M i*A i) (fun i=> N i*B i) := by
  intro i j; simp_rw [Matrix.mul_apply]; refine Lease.lists _ _ hp (fun k _=>?_); exact (h i k).times (he k j) hp
lemma Lying.powers (hp:Audience y)(h:Lying y δ M N)(r): Lying y δ (fun i=> M i^r) (fun i=> N i^r):= by induction r with| zero=> simp only [pow_zero]; exact Lying.fixed hp _| succ r ih=>simp_rw [pow_succ]; exact ih.times hp h
lemma Lying.many (hp : Audience y){J:Type}{f g:J→I→Loft F}(s:Finset J)(he:∀ i∈s,Lying y δ (f i) (g i)): Lying y δ (fun j=> ∑ i∈s,f i j) (fun j=> ∑ i∈s,g i j):= by
    intro i j; simp_rw [Matrix.sum_apply]; exact Lease.lists _ _ hp fun a ha=> he a ha i j
lemma repos (hp:Audience y)(hx:∀ i,Flash (L i) (X i))(hY:∀ i,Flash (L i) (Y i))(he: ∀ i≤e,Lying y δ (fun a=> hot (X a) i) (fun a=>hot (Y a) i)): Lying y δ (fun a=>hot (X a)⁻¹ e) (fun a=>hot (Y a)⁻¹ e) := by
  induction e using Nat.caseStrongRecOn with
  | zero=>
   let M a:=hot (X a) 0; let N a:= hot (Y a) 0
   have hv : Lying y δ (fun a=> askIT (M a)) (fun a=> askIT (N a)) := by
     intro i j; by_cases hh:i=j; swap; · simp_rw [askIT,diagonal_apply_ne _ hh]; exact Lease.const ..
     subst i; simp_rw [askIT,diagonal_apply_eq]
     have hE a: M a j j = N a j j:= ((hx a).dollar _).trans ((hY a).dollar _).symm
     simp_rw [hE]; exact Lease.same ((Weighed.constant y zero_le_one).mono (fun i=> norm_nonneg _) fun i=> priceHat (hY i) _)
   have hh:= Lying.times hp (he 0 le_rfl) hv
   have he : Lying y δ (fun a=> ace (M a)) (fun a=> ace (N a)) := by
     simp only [ace,sub_eq_add_neg]; exact Lying.plus (M:=fun _=>1) (A:= -(fun a=> M a * askIT (M a))) hp (Lying.fixed hp _) (hh.neg hp)
   simp_rw [fun i=>inclosure (hx i),fun i=> inclosure (hY i)]; exact hv.times hp (Lying.many hp (f:=fun i a=> ace (M a)^i) _ fun i _=> he.powers hp i)
  | ind n ih=>
   have hh := ih 0 (by omega) fun i hi=> he i (by omega)
   simp_rw [fun i=> invert_coin (recoupC (hx i)) n,fun i=>invert_coin (recoupC (hY i)) n]
   refine (hh.neg hp).times hp (Lying.many hp (f:=fun (p:ℕ×ℕ) i=> hot (X i) p.1 * hot (X i)⁻¹ p.2) _ fun a ha=>?_)
   obtain ⟨hm,ht⟩:= mem_filter.mp ha; have hh:= mem_antidiagonal.mp hm; exact (he _ (by omega)).times hp (ih _ (by omega) fun i hi=> he _ (by omega))
end
variable (he:Tights T S ν D' u)
include he
local notation "Ξ" => Xe (u:=u) T ν D'
local notation "♣" => Te (u:=u) T ν D'
local notation "Υ" => Ye (u:=u) X ν D' T
local notation "Ⓨ" => menu X
local notation "Δ" => chop X (1/4)
lemma yellow (hk:e≤E)(b:Letter F)(r): Twill Ⓨ Δ (fun i=> Υ i b e r) (fun i=> Υ i.wingR b e r) (fun i=> ώ T i.i):= ⟨cashIn he hk b r,(cashIn he hk b r).move Wings.wingR,(railway (chorus he) he.he hk (slot b) r).first b rfl⟩
lemma xml (hk:e≤E)(b:Letter F)(r): Twill Ⓨ Δ (fun i=> Ξ i b e r) (fun i=> Ξ i.wingR b e r) (fun i=>ώ T i.i) := by
  have ht:= (railway (clear1 he) he.he hk (slot b) r).second b rfl; rw [a_zero] at ht
  exact ⟨ht,ht.move wingR,(railway (chorus he) he.he hk (slot b) r).second b rfl⟩
lemma interlace (hk:e≤E): Lying Ⓨ Δ (fun i=> hot (♣ i) e) (fun i=>hot (♣ i.wingR) e) := by
  intro a b; have hp:= (stakesPay he hk b a).rates; have ht:= hp.transfer wingR; refine ⟨hp,ht,?_⟩
  obtain ⟨B,hB,H⟩:= ((railway (chorus he) he.he hk (slot b) (slot a)).knows b rfl a rfl).asset; refine ⟨_,hB,fun i=> ?_⟩; have h:= H i; simp only [Pi.sub_apply,hot_node,Matrix.sub_apply,map_sub] at h; exact h
lemma cashOut (hk:e≤E): Lying Ⓨ Δ (fun i=>hot (♣ i)⁻¹ e) (fun i=>hot (♣ i.wingR)⁻¹ e):= repos (X:=♣) (Y:=fun i=>♣ i.wingR) (L:=fun i=> X.S.block i.i) (sh X) (fun i=> (he.reads i).1) (fun i=> (he.reads i.wingR).1) (fun i hi=>interlace he (hi.trans hk))
end YM.RG08.Door
