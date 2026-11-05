import YM.Next.RANK.Pageant

/-! # Cumulant now from the tagged calculation on the common mask -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes
open Function Filter MeasureTheory Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Marker Cells Edition Finset
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {V Ω : Type*}
variable {C : Family G} {i k l j m p q d D a n N : ℕ}
variable {R : Lead G C.S p}
variable {hN : k≤N} {b : ℝ} {x : Points n} {hk : i<k} {h : middle C.path.levels b k ≤ i}
variable {c : Course C N p k} {τ ε : ℝ}
variable {U T} (E : StageX (d:=d) c R x b hk h q T τ U ε) (hn : n≤2)

private lemma monies_nonneg (B ε w : ℝ) (D) (h : 1 ≤ B) (he : 0 ≤ ε) (hw : 0 ≤ w) : 0 ≤ capZ B D w ∧ 0 ≤ grant₁ B ε w D ∧ 0 ≤ grant₂ B ε w D := by
  have hx := zero_lt_one.trans_le h; have hv : ∀ i:ℕ,0 ≤ Common.priced B i:=fun i=> zero_le_one.trans (priced_up i h)
  have hB := hv D; have hb := hv (2*D); have ht:=hv (2*(2*D)); unfold capZ grant₁ grant₂; dsimp only [capZ,defect]; exact ⟨by positivity,by positivity,by positivity⟩

variable (P : pennant n → poly (Chamber G C.S (i+1) p))
include hn in
private lemma onePiece (u : Marquee C k b p d x (show i+1≤k from hk)) (hp : tests x b hk (C:=C) T.2.val u) (z θ):
    (planter E (invitation (hk:=hk) P T c h) z θ).part (tale u.val).val=planted E (invitation (hk:=hk) P T c h) z u θ:= by
  unfold planter; rw [Poly.part_sum, sum_eq_single u,if_pos hp, Poly.part_send,if_pos rfl]
  · intro j _ hj;split
    · rw [Poly.part_send,if_neg]; intro he; apply hj; apply Subtype.ext; exact (yielding hn).1 (Subtype.ext he.symm)
    rfl
  simp
include hn in
private lemma noPiece (w : Twin n) (he : ¬cozy C.path.levels x b p d (walls (clim C.path.levels (i+1))) (show i+1≤k from hk) (.inr w)) (z θ):
    (planter E (invitation (hk:=hk) P T c h) z θ).part (tale (.inr w)).val=0:= by
  unfold planter; rw [Poly.part_sum]; apply sum_eq_zero; intro j _; split
  · rw [Poly.part_send,if_neg]; intro ht; apply he
    exact (yielding hn).1 (Subtype.ext ht.symm) ▸ j.property
  rfl

private lemma in_cost {_E : StageX (d:=d) c R x b hk h q T τ U ε} {g B Y L w} {u : Marquee C k b p d x (show i+1≤k from hk)}
    (H : Healthy g (dolmens x b q (walls (clim C.path.levels i)) c.allow hk.le T.1 T.2.val) U) (X : roomTest C.path.levels b k p d q)
    (hr : Metal b c R hk ε τ g B Y L) (he : 0 ≤ ε) (hv : tests x b hk (C:=C) T.2.val u) (hP : coin (P u.val) ≤ w) (hd : totalDegree (P u.val) ≤ D)
    (hp : ∀ z∈(P u.val).vars,spotP b (i+1) d (show i+1≤k from hk) (C:=C) x u.val z): ‖elegance b c x hk h T U ((R i).read (P u.val))‖ ≤ capZ B D w:= by
  unfold elegance Valve.read text; let Z:=R i; rw [pipes, Normal.reads_val,← blend_components]; let F:=P u.val
  apply le_trans (bound_v F _ hd hr.grain (fun i hi=>?_) fun i _ j _=> (hr.φ.tide ..).trans (le_trans (le_add_of_nonneg_right he) hr.wake)) (mul_le_mul_of_nonneg_right hP (zero_le_one.trans (priced_up D hr.grain)))
  exact predicts T X h hr U H i (mem_filter.mpr ⟨mem_univ _,u,hv,hp _ hi⟩)

def grant (B ε w : ℝ) (d : ℕ) :=
    let c:=capZ B d w
    let u:=grant₁ B ε w d
    u + grant₂ B ε w d + ((c+u)*u + u*c)

lemma grantNonneg (B ε w : ℝ) (d) (hb : 1≤B) (h : 0≤ε) (he : 0≤w) : 0 ≤ grant B ε w d := by
  obtain ⟨hp,hv,hL⟩:=monies_nonneg B ε w d hb h he
  exact add_nonneg (add_nonneg hv hL) (add_nonneg (mul_nonneg (add_nonneg hp hv) hv) (mul_nonneg hv hp))

-- Write with arbitrary ordinary polynomials stamped before Step (can specialize to P=Prepaced). Keeps exact-zero shapes unassigned.
include hn
theorem console (P₀ : Fin n → poly (Chamber G C.S k p)) {B θ L w Y} (H : Healthy θ (dolmens x b q (walls (clim C.path.levels i)) c.allow hk.le T.1 T.2.val) U)
    (X : roomTest C.path.levels b k p d q) (hr : Metal b c R hk ε τ θ B Y L) (he : 0 < ε) (he' : ε ≤ 1)
    (hΩ : P=polygon R P₀ (show i+1≤k from hk))
    (hV : ∀ u, Poetic (P u)) (hW : ∀ u,coin (P u)≤w) (hD : ∀ u,totalDegree (P u)≤ D)
    (hp : ∀ u,∀ z∈(P u).vars,spotP b (i+1) d (show i+1≤k from hk) (C:=C) x u z)
    (hZ : ∀ (u : Twin n), ¬cozy C.path.levels x b p d (walls (clim C.path.levels (i+1))) (show i+1≤k from hk) (.inr u) → P (.inr u)=0) :
    let V:= invitation (hk:=hk) P T c h
    let K:=glory x b p c.allow hk.le h T.1 T.2.val (anneals C c i) (polygon R P₀ hk.le T.2.val)
    ‖(leadQ E V).part (tale T.2.val).val - K U‖ ≤ grant B ε w D:= by
  intro V K; let A:= C.path.levels; let L':=planters E V; let D':= leadQ E V
  have hE : Expands D' L':=connected_spec _ (planters_one E V)
  have hC:= hr.grain; have hw:0≤w:= (Rise.sign _ _ zero_le_one).trans (hW T.2.val)
  let F:= R i; let α:= (Ship.yard C b c.allow p).hand T.1; let u := capZ B D w; let t:= grant₁ B ε w D; let z:= grant₂ B ε w D
  obtain ⟨ha,h1,h2⟩:=monies_nonneg B ε w D hC he.le hw
  let M := fun q':poly _=> dot α (elegance b c x hk h T U q'); let W:=polygon R P₀ hk.le
  let a (v : Fin n):= soloIndex x b A p d hk v; let f s j:= planted E V s j
  change ‖D'.part _-M _‖ ≤ _
  have h' j (hv : tests x b hk (C:=C) T.2.val (a j)) : D'.part (slot j)=L'.part (slot j) ∧
      L'.part (slot j)= plaids E (fun s z=> f s (a j) z) ∧
      ‖D'.part (slot j)- M (W (Sum.inl j))‖ ≤ t ∧ ‖M (W (Sum.inl j))‖≤ u:= by
    have ht : D'.part (slot j)=L'.part (slot j):= (spark_single hn hE j).symm
    have hz (v z): let q:=planter E V v z
                   (Poly.pass q).part (slot j)= f v (a j) z:= by
      intro q'; exact (selectMode _ (unquiet E V ..) j).trans (onePiece E hn P (a j) hv v z)
    have hy : L'.part (slot j)=plaids E (fun v z=> f v (a j) z):= congr_arg (plaids E) (funext fun v=> funext fun z=> hz v z)
    refine ⟨ht,hy,?_,?_⟩
    · rw [ht,hy,show W (Sum.inl j)=_ from (show W (Sum.inl j)= F.read (P (a j).val) from (by rw [hΩ]; exact page R P₀ hk j))]; exact (dominant E P X H hr he he' hV hW hD hp (a j) hv).2
    unfold M; rw [dot_norm,show W (.inl j)=F.read (P (a j).val) from (by rw [hΩ]; exact page R P₀ hk j)]; exact in_cost (_E:=E) P H X hr he.le hv (hW _) (hD _) (hp _)
  cases hv : T.2.val with
  | inl j =>
    have hx : tests x b hk (C:=C) T.2.val (a j):= by rw [hv]; exact le_rfl
    exact (le_trans (h' j hx).2.2.1 (le_add_of_nonneg_right h2)).trans (le_add_of_nonneg_right (add_nonneg (mul_nonneg (add_nonneg ha h1) h1) (mul_nonneg h1 ha)))
  | inr θ=>
    let i':= θ.val.1; let v:=θ.val.2; let sT:= (tale (.inr θ)).val
    let p₁:= P (Sum.inl i'); let p₂:=P (Sum.inl v); let p':= F.read (P (.inr θ)); let D₁:=D'.part (slot i');let D₂:= D'.part (slot v)
    have hi₁:tests x b hk T.2.val (a i') (C:=C):= by rw [hv]; exact singleton_subset_iff.mpr (mem_insert_self ..)
    have hi₂:tests x b hk T.2.val (a v) (C:=C):= by rw [hv]; exact singleton_subset_iff.mpr (mem_insert_of_mem (mem_singleton_self v))
    obtain ⟨hq,hb,hX,hA⟩:= h' i' hi₁
    obtain ⟨hr',hd',hd1,hd2⟩:= h' v hi₂
    let g j z:=f j (a i') z*f j (a v) z
    have hz:= entangles E P X H hr he he' hV hW hD hp (a i') (a v) hi₁ hi₂
    have Hf : ‖plaids E g-M (F.read (p₁*p₂))‖ ≤ z:=hz.2
    -- aggregate higher. even when the pair didn't previously exist.
    let β v θ:=(planter E V v θ).part sT
    have hm i z : (Poly.pass (planter E V i z)).part sT= β i z+g i z:= by
      rw [crossings hn (show Expands (planter E V i z) _ from ⟨unquiet E V i z,rfl⟩)]
      -- Needs both particle slots on same measure
      change _+ (planter E V i z).part (slot i')*(planter E V i z).part (slot v)=_; exact congr_arg (_+·) (congr_arg₂ (·*·) (onePiece E hn P _ hi₁ i z) (onePiece E hn P _ hi₂ i z))
    have hℓ : (∀ j, letI:= (E.tag j).M; Integrable (β j) (E.tag j).μ)∧ ‖plaids E β-M p'‖≤t:= by
      by_cases hh : cozy A x b p d (walls (clim A (i+1))) (show i+1≤k from hk) (.inr θ)
      · let j':= (⟨Sum.inr θ,hh⟩ : Index x b A p d hk); have hx : tests (C:=C) x b hk T.2.val j':= by rw [hv]; exact le_rfl
        have Hh : β= fun i z=> f i j' z:= funext (fun i=> funext fun z=> onePiece E hn P j' hx i z)
        rw [Hh]; exact dominant E P X H hr he he' hV hW hD hp j' hx
      rw [show β=(fun i z=>0) from funext fun i=>funext fun z=> noPiece E hn P θ hh i z]
      refine ⟨fun j=>?_,?_⟩
      · letI:=(E.tag j).M; exact integrable_zero _ _ _
      rw [plaid_const,show M p'=0 from (by unfold p' M elegance text; simp only [hZ _ hh,map_zero,dot_zero]),sub_self,norm_zero]; exact h1
    have hy : D'.part sT+D₁*D₂= plaids E β + plaids E g := calc
      _ = L'.part sT:= (crossings hn hE θ).symm
      _ = plaids E (fun j z=> β j z+g j z):= congr_arg (plaids E) (funext fun j=> funext fun z=> hm j z)
      _ = _ := plaids_add E β _ hℓ.1 hz.1
    let a₁:=M (W (.inl i')); let a₂:=M (W (.inl v)); have Hx:D'.part sT=plaids E β+plaids E g-D₁*D₂:= eq_sub_of_add_eq hy
    have H₁ : M (W (.inr θ)) = M p'+ M (F.read (p₁*p₂)) - a₁*a₂:= by
      have H' : W (.inr θ)= p'+ F.read (p₁*p₂)- W (.inl i') * W (.inl v):= by dsimp only [W,p',p₁,p₂]; rw [hΩ]; exact second_page R P₀ hk θ
      rw [H']; unfold a₁ a₂ M elegance text; rw [map_sub,_root_.map_add,map_mul (f:=aeval (R:=ℂ) (S₁:=ℂ) _) (W (.inl i')) (W (.inl v)), circle_diff]
    change ‖D'.part sT-M _‖ ≤ _
    have ht : ‖D₁‖ ≤ u+t:= (le_trans (le_of_eq (congr_arg norm (sub_add_cancel D₁ a₁).symm)) (norm_add_le ..)).trans (le_trans (add_le_add hX hA) (by rw [add_comm]))
    rw [Hx,H₁]; let q:= M p'
    rw [show plaids E β+plaids E g-D₁*D₂ - (q +M (F.read (p₁*p₂))-a₁*a₂)= (plaids E β-q)+(plaids E g-M (F.read (p₁*p₂)))-(D₁*D₂-a₁*a₂) by abel]
    exact (norm_sub_le ..).trans (add_le_add ((norm_add_le ..).trans (add_le_add hℓ.2 Hf)) (indiv hX hd1 ht hd2))
end YM.Next.Rank.Tapes
