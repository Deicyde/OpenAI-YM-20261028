import YM.Push.RELAY_DIFFERENCE.Placement
import YM.Next.PHASE.Roots

/-!
# Cards: complete products, discrepancy phase transfer physical ledger

Allows full mixed budgets on the same law without
throwing away price differences between different grades.

Root and interior
bounds include subtraction of the projected portion (when F is a discrepancy)
even in slots where the accompanying ext factors are going to have a much
worse individual moment estimate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cards
open MeasureTheory Function Filter Set Lattice Cells Wilson Extraction Word Push Next.Phase
open Push.RelayDifference
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
variable {G:Gauge} {C:Family G} {S:Schedule}
variable {n : Side} {N p k k' : ℕ}
set_option quotPrecheck false
local notation "R"=>S.side N p
variable {β A:ℝ}{F: Config G (S.side N p)→ℂ}

structure PaidAt (S:Schedule)(N p k:ℕ)(β A:ℝ)(F:Config G (S.side N p)→ℂ): Prop where
   live : k≤N
   ticket : Interior ((center S p live 0).chamber 0) F
   mark : (center S p live 0).rootTest β F ≤ A

variable (h : PaidAt S N p k β A F) {W W₀ : Tiling (S.side N p)}
include h
lemma PaidAt.cost : 0 ≤ A := ((center S p h.live 0).root_nonneg β _).trans h.mark
lemma PaidAt.act (b : Bool)(s:Signed)(he:diag s) : PaidAt S N p k β A (RelayDifference.oriented F b s 0) := ⟨h.live,
    center_interior h.live s he b _ h.ticket, (center_price h.live _ F b s he h.ticket β).le.trans h.mark⟩
lemma PaidAt.stars : PaidAt S N p k β A (fun u=> star (F u)):= by
    rw [show (fun u=> star (F u)) = RelayDifference.oriented F true 1 0 from funext fun u=>by simp [RelayDifference.oriented,hand]]
    exact h.act true _ rfl

omit h in
lemma literal_or (F: Config G n→ℂ)(b:Bool)(s:Signed): literal (RelayDifference.oriented F b s):=by
    intro x y; funext u; unfold RelayDifference.oriented; simp only [comp_apply, ← pull_one,pull_pull,one_mul, affine,Signed.act_one]
lemma PaidAt.smaller (b:Bool)(s:Signed)(he:diag s) (ht : Cells.span S h.live p ∣ W.side.val)
    {u: Site R}(hs:u∈ W.margin 0 (3*Cells.span S h.live p))(hβ:Seam G (S.side N p) β) :
      Interior (W.chamber 0) (RelayDifference.oriented F b s u) ∧ W.rootTest β (RelayDifference.oriented F b s u) ≤ A:=
    offset h.live W β A ht (literal_or F b s) hβ (h.act b s he).ticket (h.act b s he).mark hs

variable (W)
lemma PaidAt.at_cell (b:Bool)(s:Signed)(he:diag s) (ht:Cells.span S h.live p ∣ W.side.val)
    {i : W.Cell}{u:Site R}(hs:u∈ W.margin i (3*Cells.span S h.live p))(hβ:Seam G (S.side N p) β) :
    ∃ v:Site R, ∃ χ:Bool, ∃ q:Signed, v∈ W.margin 0 (3*Cells.span S h.live p) ∧ W.copyMap i v=u ∧ diag q ∧
       W.copy i (RelayDifference.oriented F χ q v) = RelayDifference.oriented F b s u ∧ Interior (W.chamber 0) (RelayDifference.oriented F χ q v) ∧ W.rootTest β (RelayDifference.oriented F χ q v) ≤ A :=by
    obtain ⟨y,hy⟩ := W.pointed i u; let χ:= (decide (W.hand i)).xor b; let q:= (W.omega i)⁻¹*s
    have hp: diag q := diag_mul (diag_inv (show diag (W.omega i) from rfl)) he
    have hu : y∈ W.margin 0 (3*Cells.span S h.live p) := (W.reflected_margin _ _ _).mpr (hy.symm ▸ hs)
    refine ⟨y,χ,q,hu,hy,hp,?_,h.smaller χ q hp ht hu hβ⟩; unfold q χ; rw [copied,hy,mul_inv_cancel_left]; cases b <;> cases he : decide (W.hand i) <;> rfl
lemma PaidAt.any (ht:Cells.span S h.live p ∣ W.side.val)
    {i:W.Cell}{u:Site R}(hs:u∈ W.margin i (3*Cells.span S h.live p))(hβ:Seam G (S.side N p) β):
    ∃ G':Config G (S.side N p) → ℂ, W.copy i G' = F ∘ translate u ∧ Interior (W.chamber 0) G' ∧ W.rootTest β G' ≤ A :=by
    obtain ⟨v,b,s,-,-,-,hx,he⟩:= h.at_cell W false _ (show diag 1 from rfl) ht hs hβ; refine ⟨_,?_,he⟩; rw [hx]; funext U; rw [RelayDifference.oriented,pull_one]; rfl
omit h
variable {W}
private lemma copy_prod (i : W.Cell) (F : ι → Config G (S.side N p) → ℂ) (U : Config G (S.side N p)) :
    W.copy i (fun x=> ∏ i, F i x) U = ∏ j,W.copy i (F j) U := by
    by_cases h : W.hand i <;> simp [Tiling.copy,h,star_prod]
-- can't use `PaidAt.live` when empty group, ask antecedent

lemma exterior (hw : W₀.kind=.link) (he:W.kind=.link) (hx: W₀.base=W.base) (hW: W₀.side.val ∣ W.side.val)
    (hp:k ≤ N) (ht: Cells.span S hp p ∣ W₀.side.val)
    (u: ι → Site R) (F:ι → Config G (S.side N p)→ℂ) (A:ι→ℝ) (i:W.Cell) (hf:∀ j,W.which (u j)=i)
    (hM:∀ j,Inside W₀ (3*Cells.span S hp p) (u j)) (hS:∀ i j:ι,i≠j→ W₀.side.val < separation (u i) (u j)) (h:∀ j,PaidAt S N p k β (A j) (F j)) (hβ:Seam G (S.side N p) β) :
    ∃ Z: Config G (S.side N p)→ℂ, W.copy i Z=(fun V=> ∏ j,(F j ∘ translate (u j)) V)∧
         Interior (W.chamber 0) Z ∧ W.rootTest β Z ≤ ∏ j,A j := by
    let d:=Cells.span S hp p; let M:=3*d; have hg(j:ι):u j∈ W.margin i M:= by rw [← hf j]; exact shared_inside W W₀ hx hw he hW M _ (hM _)
    choose v b s hv hu ht' hr hI hC using fun j:ι=> (h j).at_cell W false 1 rfl (ht.trans hW) (hg j) hβ
    let g j:= RelayDifference.oriented (F j) (b j) (s j) (v j); let Z U:=∏ j,g j U
    let z(x:W.Cell×ι):= W.copyMap x.1 (v x.2); let c (i:W.Cell×ι):= W₀.which (z i)
    have hy (x:W.Cell × ι): Inside W₀ M (z x) :=
      (inside_reflected W W₀ hx hW he hw x.1 ..).mpr
        ((inside_reflected W W₀ hx hW he hw i ..).mp (hu x.2|>.symm ▸ hM x.2))
    have hG(x:W.Cell ×ι): W.which (z x)=x.1:= W.which_chamber (W.enumerate _ (show v x.2∈ W.chamber 0 from (hv _).1))
    have hJ: Injective c:= by
       rintro ⟨x,I⟩ ⟨y,J⟩ h; have he:= shared_cell W W₀ hx hW h; rw [hG,hG] at he; obtain rfl:x=y:=he
       congr 1; by_contra he
       have ht:=W₀.extent (hy (x,I)).1 (x := z (x,I)) (y:= z (x,J)) (show z (x,J)∈ W₀.chamber (c (x,I)) from h ▸ (hy (x,J)).1)
       have hh : separation (z (x,I)) (z (x,J))=separation (u I) (u J) := by dsimp only [z]; rw [separation_copy,← separation_copy W i,hu,hu]
       exact (hS I J he).not_ge (hh ▸ ht)
    have ha(x:W.Cell×ι):∃ G':Config G (S.side N p)→ℂ,W.copy x.1 (g x.2) = W₀.copy (c x) G' ∧ Interior (W₀.chamber 0) G' ∧ W₀.rootTest β G' ≤ A x.2:= by
       rcases x with ⟨i,j⟩; unfold g; rw [copied]
       obtain ⟨v,b,s,-,-,-,he,ht⟩:= (h j).at_cell W₀ ((decide (W.hand i)).xor (b j)) (W.omega i * s j) (diag_mul (show diag (W.omega i) from rfl) (ht' _)) ht (hy (i,j)) hβ
       exact ⟨_,he.symm,ht⟩
    choose G' hH ha hb using ha; refine ⟨Z,funext (fun U=> ?_), Interior.combines _ _ (fun i _=>hI i),?_⟩
    · unfold Z; rw [copy_prod]; refine Finset.prod_congr rfl fun j _=>?_ ; unfold g; rw [hr,RelayDifference.oriented,pull_one]; rfl
    have hh : W.fullAt (fun _=> Z) = fun U=>∏ i : W.Cell × ι, W₀.copy (c i) (G' i) U:=by
       funext U; rw [Fintype.prod_prod_type]; unfold Tiling.fullAt Z; refine Finset.prod_congr rfl fun i _=>?_ ; rw [copy_prod]; exact Finset.prod_congr rfl fun j _=> congr_fun (hH (i,j)) U
    apply le_of_pow_le_pow_left₀ W.cells_positive.ne' (Finset.prod_nonneg (fun j _=>(h j).cost))
    rw [W.powering]; change ‖moment β (W.fullAt _)‖ ≤ _; rw [hh]; apply le_trans ((W₀.planted hβ _ hJ G' ha).trans (Finset.prod_le_prod (fun i _=> W₀.root_nonneg ..) (fun i _=> hb i)))
    rw [Fintype.prod_prod_type]; simp

private lemma collect {α : Type*} [Fintype α] {U : Type*} [CommMonoid U] (f : κ → α)
    [(i : α) → Fintype {x // f x=i}] (g : κ → U) :
    (∏ i : α, ∏ j : {x // f x=i}, g j.val)=∏ j : κ,g j := by
    have he:= Equiv.prod_comp (Equiv.sigmaFiberEquiv f) g; rw [Fintype.prod_sigma] at he; exact he

lemma plant (hw : W₀.kind=.link)(he:W.kind=.link) (hx: W₀.base=W.base) (hW: W₀.side.val ∣ W.side.val)
    (hp:k ≤ N) (ht: Cells.span S hp p ∣ W₀.side.val) (hk:k' ≤ N) (hs: Cells.span S hk p ∣ W.side.val)
    (u: κ → Site R) (F:κ → Config G (S.side N p)→ℂ) (A:κ→ℝ)
    (v:ι → Site R) (Z:ι→ Config G (S.side N p)→ℂ)(B:ι→ℝ)
    (hM:∀ j, Inside W₀ (3*Cells.span S hp p) (u j))(hS:∀ i j:κ,i≠j→ W₀.side.val < separation (u i) (u j))
    (hV:∀ j, Inside W (3*Cells.span S hk p) (v j))(hZ:∀ i j:ι,i≠j→W.side.val < separation (v i) (v j))
    (hQ:∀ (i:ι)(j:κ),W.side.val < separation (v i) (u j))
    (h:∀ j,PaidAt S N p k β (A j) (F j))(hr:∀ j,PaidAt S N p k' β (B j) (Z j))(hβ:Seam G (S.side N p) β):
    ‖moment β (fun U => (∏ i:ι, (Z i ∘ translate (v i)) U)*∏ j:κ,(F j ∘ translate (u j)) U)‖ ≤ (∏ i:ι,B i)*∏ j:κ,A j:=by
    classical
    let c (i:ι):= W.which (v i); let x (i:κ):= W.which (u i); let s:= Set.range x; let f:κ→s:= Set.rangeFactorization x; let D:= Sum.elim c (fun i:s=> i.val)
    letI:Fintype s:= Fintype.ofFinite _; have hi:Injective c:=by intro i j h; by_contra h'; exact (hZ i j h').not_ge (W.extent (v:=c i) (hV i).1 (h ▸ (hV j).1))
    have hC i (a : s) : c i≠a.val:=by obtain ⟨j,h⟩:=a.property; rw [← h]; intro hh; exact (hQ i j).not_ge (W.extent (v:=c i) (hV i).1 (hh ▸ (shared_inside W W₀ hx hw he hW _ _ (hM j)).1))
    have hT:Injective D:=by rintro (i|i) (j|j) h; rw [hi h]; exact (hC i j h).elim; exact (hC j i h.symm).elim; rw [Subtype.ext (show i.val=j.val from h)]
    choose G1 hG1 hI hA using fun i=> (hr i).any W hs (hV i) hβ
    choose G2 hG2 hJ hB using fun i:s=> exterior (ι:={x//f x=i}) hw he hx hW hp ht (fun j=>u j.val) (fun j=>F j.val) (fun j=> A j.val) i.val
      (fun j=>congrArg Subtype.val j.property) (fun j=> hM _) (fun j l h=> hS _ _ (Subtype.val_injective.ne h)) (fun j=>h _) hβ
    let M:=Sum.elim G1 G2; let W':=Sum.elim (fun i : ι=> B i) (fun i:s=> ∏ j:{x// f x=i}, A j.val); have ht i : W.rootTest β (M i) ≤ W' i:= by rcases i with i|i; exact hA _; exact hB _
    have hv(U:Config G R) : (∏ i:ι, (Z i ∘ translate (v i)) U)*(∏ j:κ,(F j ∘ translate (u j)) U)=∏ i,W.copy (D i) (M i) U:=by
       rw [Fintype.prod_sum_type, ← collect f (fun j=> (F j ∘ translate (u j)) U)]; simp only [D,M,Sum.elim_inr,Sum.elim_inl,c,hG1,hG2]
    rw [funext hv]; apply le_trans ((W.planted hβ D hT M (by rintro (i|i); exacts [hI _,hJ _])).trans (Finset.prod_le_prod (fun i _=> W.root_nonneg ..) (fun i _=> ht i))); unfold W'; rw [Fintype.prod_sum_type]; simp only [Sum.elim_inl,Sum.elim_inr]; rw [collect f A]
end YM.OPE.Cards
