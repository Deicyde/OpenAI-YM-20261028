import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Deck.Festal
/-! # True form Nary, hence plate/kernel assets descend through actual clock. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Deck.Stellar
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {c f C F:Side} {P : Patch} {M : ℕ} {K : Teller G}
variable {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q:KernelChoices} {hC : C.val=c.val*M} {he:2 ≤ c.val}
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
variable {T: Tube G (stepped Q h)} {T': Tube G (stepped Q H)} {p : ℝ} {E: Forest (stepped Q h).ratio} {E':Forest (stepped Q H).ratio}
    {X: Coat T E} {X': Coat T' E'} (A : Stellar hC he K p X X')
local notation "B" => radiusB p
abbrev target (v:Lace h H M) (k:Coat.Target C F G):Coat.Target c f G := Prod.map (men v) id k
abbrev seed (v:Lace h H M) (p:Tubular F G): Tubular f G:=Prod.map (curr v.high.cut) id p
lemma seek (hC : C.val=c.val*M) (he : 2 ≤ c.val): Nest (Deck.divides hC) (men (Lace.project (h:=h) (H:=H) hC he)) (Coat.root (Y)) (Coat.root (S)) := by
  have hs := rod_nests (h:=h) (H:=H) (Q:=Q) hC he
  let L' := Lace.project (h:=h) (H:=H) hC he
  refine ⟨fun z=>?_,fun x i hi=>?_,fun i j hh hj=>?_⟩
  · unfold Coat.root; simp only [men,Prod.map_fst,Prod.map_snd,id_eq]; rw [← usual,hs.footing]
  · rcases i with ⟨s,i⟩; obtain ⟨j,hp,hT⟩:= hs.extend (s⁻¹.act x) i (by change s.act (focus (stepped Q h) i)=_ at hi; rw [← usual,← hi,s.inv_act])
    exact ⟨(s,j),Prod.ext rfl hp,(congr_arg s.act hT).trans (by rw [← Signed.act_mul, mul_inv_cancel,Signed.act_one])⟩
  have ht : i.1=j.1:=congr_arg (fun i:Mention c f=>i.1) hh
  refine Prod.ext ht (hs.firm _ _ (congr_arg (fun i : Mention c f=> i.2) hh) ?_); unfold Coat.root at hj; rw [ht] at hj; exact j.1.act_injective hj
lemma tempnest (hC : C.val=c.val*M) (he : 2 ≤ c.val):Nest (Deck.divides hC) (seed (G:=G) (Lace.project (h:=h) (H:=H) hC he)) (along (Y)) (along (S)):= (Deck.footing (h:=h) (H:=H) hC he|>.pr (E:=Axis)).pr (E:=G.ColorIndex)
include A
lemma radiant : Nary (divides hC) (target (L)) (seed (L)) (aim (Y)) (along (Y)) (aim (S)) (along (S)) X'.form X.form ((B)/4):= by
  have hc:=tempnest (Q:=Q) (G:=G) (h:=h) (H:=H) hC he; have hq:= (seek (Q:=Q) (h:=h) (H:=H) hC he).pr (E:=G.ColorIndex)
  have hP:= A.old; have hr:= A.wall
  have hx: 2*((B)/4)< c.val:= by have hv:=A.news; omega
  have hb' i j (hj : ¬separation (aim (Y) i) (along (Y) j) ≤ (B)/4) : X'.form i j=0 := X'.plume (A.reached.symm ▸ A.wall) i j (by rw [A.D.1]; exact lt_of_not_ge hj)
  refine ⟨hq,hc,hx, fun i j hi =>?_,fun i j hj=> by by_contra ha; exact hj (hb' i j ha),fun i j hj=> by by_contra! hn; rw [← A.D.2] at hn; exact hj (X.plume (A.equal.symm ▸ A.old) i j hn)⟩
  let j':= seed (L) j; let k:= target (L) i; let v:= Deck.light (L).high.cut (sing j')
  obtain ⟨b,d,hH,hE⟩:= hr.accepted.feeds; obtain ⟨z,g,hS,hQ⟩:= hP.accepted.feeds; rw [← hr.accepted.high] at hH; rw [← hP.accepted.high] at hS
  have hK p: stand v p= (Pi.single j' (1:ℝ):Tubular f G→ℝ) (seed (L) p):= congr_fun (singled j') (seed (L) p)
  have hz:X'.form i j=(X'.form *ᵥ stand v) i:= by
    unfold Matrix.mulVec dotProduct; rw [Finset.sum_eq_single j ?_ ?_]
    · rw [hK j,show seed (L) j=j' from rfl,Pi.single_eq_same,mul_one]
    · intro b _ hb; by_cases he':separation (aim (Y) i) (along (Y) b)≤(B)/4
      · rw [hK b,Pi.single_eq_of_ne (show seed (L) b≠j' from fun hh=> hb (hc.point hx _ _ _ he' hi hh)),mul_zero]
      change X'.form i b *_=_; rw [hb' i b he',zero_mul]
    simp
  rw [hz,← X'.charged_for hH]; unfold stand; rw [show X'.motion v i.1=X.motion (sing j') (men (L) i.1) from A.motionB ..]; rfl

lemma plank (D:ℕ) (he : 2*(D+B)<c.val) (_hx:(B)/4 ≤ D) (i j:Tubular F G) (hp:separation (along (Y) i) (along (Y) j)≤D) :
    X'.plate i j=X.plate (seed (L) i) (seed (L) j) := by
  have H':= A.radiant; let x:= along (Y) i; let y:=along (Y) j; let i':= seed (L) i; let j':=seed (L) j
  have hc:2*D<c.val:=by omega
  unfold Coat.plate; simp only [Matrix.add_apply, Matrix.mul_apply,Matrix.transpose_apply]; apply congr_arg₂ (fun x y:ℝ=>x+y) ?_ ?_
  · apply H'.warps.all _ x H'.fits
    · intro k hk; rw [show X'.form k i=0 from not_ne_iff.mp (mt (H'.old _ _) (by rw [separation_comm]; exact hk)),zero_mul]
    · intro k hk
      rw [show Macrame.splitter _ x=_ from H'.wefts.footing i] at hk
      rw [show X.form k (seed (L) i)=0 from not_ne_iff.mp (mt (H'.new _ _) (by rw [separation_comm]; exact hk)),zero_mul]
    intro k hk
    rw [H'.pays k i (by rw [separation_comm]; exact hk)]; apply congr_arg
    let b:=aim (Y) k; have hy : separation b y ≤ D+B:= by apply (separation_triangle b x y).trans; rw [separation_comm b]; change separation x b ≤ (B)/4 at hk; change separation x y≤D at hp; omega
    by_cases hd: separation b y≤(B)/4
    · exact H'.pays _ _ hd
    rw [not_ne_iff.mp (mt (H'.old _ _) hd),show X.form (target (L) k) (seed (L) j)=0 from not_ne_iff.mp (mt (H'.new _ _) ?_)]
    rw [← H'.warps.footing,← H'.wefts.footing,← teaches (divides hC) b y ((Nat.mul_le_mul_left 2 hy).trans_lt he)]; exact hd
  · by_cases hd:i=j
    · subst j; unfold sleepy; rw [diagonal_apply_eq,diagonal_apply_eq]
      rw [clean_c X' A.dawn,clean_c X A.snow,show (i.1∉ E'.trunks)↔(seed (L) i).1∉ E.trunks from (A.tree.pines _).not]
    unfold sleepy; rw [diagonal_apply_ne _ hd, diagonal_apply_ne _ (show i'≠ j' from fun he=> hd (H'.wefts.point hc x i j (by unfold x; rw [separation_self]; omega) hp he))]
lemma caput (i : Tubular F G): X'.linearBill i=X.linearBill (seed (L) i):= by
  have H:= A.radiant; let j:= seed (L) i
  unfold linearBill Matrix.mulVec dotProduct; simp only [transpose_apply]; apply H.warps.all _ (along (Y) i) H.fits
  · intro k hk; rw [separation_comm] at hk; rw [not_ne_iff.mp (mt (H.old _ _) hk),zero_mul]
  · intro k hk; rw [H.wefts.footing, separation_comm] at hk; rw [not_ne_iff.mp (mt (H.new _ _) hk),zero_mul]
  intro k hk; rw [separation_comm] at hk; rw [H.pays _ _ hk]; exact congr_arg (fun x:G.Color=>X.form _ _*x k.2) (A.priceB ..)
end YM.PhysicalNext.Repeat.Deck.Stellar
