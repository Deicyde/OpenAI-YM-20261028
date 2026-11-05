import YM.Next.RANK.Patchable
import YM.Next.RANK.Tail
import YM.Next.RANK.Waterfall

/-!
# Exact vacuum re-expression at starting k

Candle output on unchanged (G,C,β,k,N,p). Does not assert that another vStep
picks up this representation and produces later ones. Supplies exponent reparations
and exact vertex factors for marker re-expression too.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Alarm
open Function Filter RG Thirst Baler Lattice Wilson Finset MeasureTheory Relation Corona Value Glyph Marker PathData
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {P : Rep G n} {ι κ V : Type}
variable {A : PathData G} {X : Activities G n} {p q : BudgetPoint} {c : Clip} {u r e m Y σ C Λ v δ w β : ℝ}

def breath (D Z : ℝ) (q : BudgetPoint) (β : ℝ) (_ : ℝ) :=wilt q.B * (β*outTail D Z q.B)
def water (D : ℕ) (Λ : ℝ) (p q : BudgetPoint) (β e : ℝ) := wilt q.B*(β*(2* sourceCharge D (e+2) Λ p.threshold))

def swollen (q p : BudgetPoint) (c : Clip) (σ e : ℝ) := Lower p q ∧ scalesExp p q (e+2) ∧ 2000000*(e+2)≤ σ*q.B ∧ Turnon c q.threshold q.B

def vacancies (e Λ σ A δ b : ℝ) (p q : BudgetPoint) := breath σ A q b e+water 2 Λ p q 1 e+
    water 3 A p q b e+water 4 A p q b e+wilt q.B*(Real.exp (100000*(e+2))*δ)

def rupture (A : PathData G) (p q : BudgetPoint) (c : Clip) (β : ℝ) (U : Config G n) :=
    -β*(Shift c p.threshold q.threshold U+rag (basin A q.B c p.threshold q.threshold) U)

def loose (A : PathData G) (X : Activities G n) (c : Clip) (β : ℝ) (p q : BudgetPoint) (U : Config G n) := -(A.inChannels c p β U - A.inChannels c q β U) -
    rupture A p q c β U + eng X p q U

lemma pledges {β : ℝ} (hb : 0≤β) (H : A.Bounds c σ C Λ) (he : X.Valid p δ w) (hp : swollen q p c σ e) (hq : 0≤e) :
    Volunteer (loose A X c β p q) q (e+1) (vacancies e Λ σ C δ β p q) := by
  obtain ⟨ℋ,L,hT,hX⟩:=hp
  let b:= q.B; let t:= p.threshold;let τ:=q.threshold
  let G1:= atomGift (n:=n) A.cubic p q
  let G2:= atomGift (n:=n) A.quartic p q
  let G3:= atomGift (n:=n) A.loop p q
  let f: Config G n→ℝ:=fun U=> baseGift A p q c U-basin A q.B c p.threshold q.threshold U
  let PX (F : Config G n→ ℝ) (r : ℝ):=fun U=> -r*rag F U
  have ε : 0≤ e+1:= add_nonneg hq zero_le_one
  have hR : e+1+1=e+2:=by ring
  have hx := tailing A hX ℋ.good ℋ.size q.threshold_pos H (show 0≤e+1+1 from add_nonneg ε zero_le_one)
    (show 2000000*(e+1+1)≤σ*q.B from hR.symm ▸ hT) q rfl (n:=n)
  have hf:Volunteer (PX f β) q (e+1) (breath σ C q β e) := by
    have ht:=blossom hx ε f (fun i=> earning A hX ℋ.good ℋ.size q.threshold_pos H i rfl rfl) (-β); simpa only [abs_neg,abs_of_nonneg hb] using! ht
  have hs (j) (F : ℕ → Atom G j) (Z y : ℝ) (hy : 0≤ y) (hh : ∀ i,(F i).Invariant) (hg : SumBudget (fun i=> (F i).budget σ) Z) : Volunteer (PX (atomGift F p q) y) q (e+1) (water j Z p q y e) := by
    have hz := cent_cost F p q hg hh ℋ.good ℋ.size (e+1+1) (add_nonneg ε zero_le_one) (show 200000*(e+1+1)≤ σ*q.B by linarith only [hT,hq]) (n:=n)
    have hu:=blossom hz ε _ (fun U=>level F p q H.width hg hh ℋ.good U) (-y); simpa only [hR,abs_neg,abs_of_nonneg hy] using! hu
  have hi:loose A X c β p q= PX f β + PX G3 1+PX G1 β+PX G2 β+eng X p q := by
    ext z; have hz:(f+(basin A b c t τ))=baseGift A p q c := by ext U; simp [f,b,t,τ]
    have he:rag (baseGift A p q c) z=rag f z+ rag (basin A b c t τ) z:= by rw [← hz]; exact rag_add ..
    simp only [loose,PX,Pi.add_apply,law_shift A p q c β ℋ.good z]; unfold rupture; rw [he]; dsimp only [G1,G2,G3,b,τ,t]; ring
  rw [hi]; unfold vacancies; rw [show e+2=e+1+1 from hR.symm]
  exact Volunteer.add ε (Volunteer.add ε (Volunteer.add ε (Volunteer.add ε hf (hs _ _ _ _ zero_le_one (fun i=> (H.invariant i).1) H.two))
     (hs _ _ _ _ hb (fun i=> (H.invariant i).2.1) H.three)) (hs _ _ _ _ hb (fun i=> (H.invariant i).2.2) H.four))
      (once X he ℋ (e+1) ε (by rw [hR];exact L))

def plane (w e : ℝ) := (83521 : ℝ)* (Real.exp (100000*(e+1))*w)

-- expose signature
structure Drama (A : PathData G) (P : Activities G n) (c : Clip) (β δ v w σ C Λ : ℝ) (p q : BudgetPoint) (U : ℝ) : Prop where
  squeeze : swollen q p c σ v
  wide : q.supportExponent ≤ v
  entitled : vacancies v Λ σ C δ β p q ≤ 1/4
  hale : 2*U ≤ β*c.linear/5 * q.threshold^2
  cost : 0 ≤ U
  site (t : ℝ) (h : t=2*vacancies v Λ σ C δ β p q+ plane w v+batch U (v+1) q.B) :
    t ≤ 1/4 ∧ (↑((q.B+q.B+1)^4:ℕ):ℝ)*t ≤ 1


private lemma longest (A : Activities G n) (R : Neat n → Burst G n p.threshold) (Y : Equiv ℕ (Neat n × ℕ)) (x : Neat n) (U) :
    Archive (Baler.lengthen A p R Y) x U= (R x).value U:= by
  unfold Archive; rw [tsum_eq_single (Y.symm (x,0)), if_pos, Baler.lengthen]; simp only [Y.apply_symm_apply,↓reduceIte]
  · apply Subtype.ext; unfold lengthen meterAddress anchor; simp [Y.apply_symm_apply]
  intro b hb
  change (if _ then if (Y b).2 = 0 then ((R (Y b).1).value U) else _ else _)=_
  split_ifs with h hx
  · have hz : (Y b).1=x:= Subtype.ext (congr_arg Subtype.val h); exact False.elim (hb (Y.injective (by rw [Y.apply_symm_apply]; exact Prod.ext hz hx)))
  all_goals rfl

private lemma uniqueR {A : Activities G n} {τ : ℝ} {R T : Neat n→Burst G n τ} (h : ∀ i,(R i).city=i) (g : ∀ i,(T i).city=i)
    (hx : ∀ i x,(R i).value x=Archive A i x) (hy : ∀ i x,(T i).value x=Archive A i x) : R=T:= by
  ext1 i;have H:= (h i).trans (g i).symm; have hz:=funext (fun x=>(hx i x).trans (hy i x).symm); generalize R i=r at H hz ⊢; generalize T i=t at H hz ⊢; cases r;cases t; congr

-- bound exponent monotone
lemma SumHit.raised {S : ι→Burst G n p.threshold} {e u v : ℝ} (h : SumHit (p:=p) S v u) (H : e ≤ v) : SumHit (p:=p) S e u := by
  obtain ⟨m,hm,he⟩:=h
  refine ⟨m,hm,fun i=>?_⟩
  let f e := pay (fun t=> m t* debt p.B e (S t).city.val.1) (fun t=> i∈(S t).city.val.1)
  have hf t:0≤ f e t:= by unfold f pay; split; exact mul_nonneg (hm _).1 (Real.exp_pos _).le; exact le_rfl
  have hE t:f e t≤ f v t:= by unfold f pay; split; exact mul_le_mul_of_nonneg_left (debt_mono _ H _) (hm t).1; exact le_rfl
  have hv:= (he i).2.1.of_nonneg_of_le hf hE
  exact ⟨hf,hv,(hv.tsum_le_tsum hE (he i).2.1).trans (he i).2.2⟩

-- operative output. cost at q from this stamp
def Agreed (P : Rep G n) (p' : BudgetPoint) (Q : Rep G n) := Q.path=P.path∧ Q.clip=P.clip ∧ Q.activities.reg=P.activities.reg ∧ Q.activities.E=P.activities.E ∧ Q.p=p' ∧ Q.beta=P.beta ∧ Q.v=P.v
structure Bridges (P : Rep G n) (Q : Rep G n) (v u σ C Λ δ : ℝ) (X : Siren G n q.threshold) (W : ValidX n → Wickless G n q.threshold) : Prop where
  precise : Agreed P q Q
  birth : Peace X
  head : fertile (q:=q) X u (v+1) (batch u (v+1) q.B)
  tails : Garden W
  remain : Verse W q (v+1) (2*vacancies v Λ σ C δ P.beta P.p q)
  predicts U : Real.exp (P.exponent U) = Real.exp (Q.exponent U)* (∏ i,((W i).value U+1)) * ∏ i∈flags q.threshold U, X.value i U
  jacket R (hr : ∀ i : Neat n,(R i : Burst G n P.p.threshold).city=i) (he : ∀ i U,(R i).value U=Archive P.activities i U) i U :
    let V := (Empty.elim : Empty → Site n)
    column (teat (enroll V ∘ R) (fun x=> (W x).credit V) X) i U=(↑(Archive Q.activities i U):ℂ)

-- propagate concrete Psi stamps after β across rest not done

lemma reductions (H : P.Lawful σ C Λ δ w) (hb : 0≤P.beta) (Y : Drama P.path P.activities P.clip P.beta δ v w σ C Λ P.p q u) :
    ∃ X W Q, Bridges (q:=q) P Q v u σ C Λ δ X W ∧ Q.eval=P.eval ∧ Q.Lawful σ C Λ δ (Real.exp (-u)) := by
  let p:=P.p; let A:=P.activities;let C':=P.clip; let Z:= P.path; let b:=P.beta
  have hp:= H.paths; have hq:= H.labels; have hv:= Y.squeeze.1; have he:=Y.squeeze.2.2.2
  have hz : P.p.supportExponent ≤ v:= hv.still▸ Y.wide
  have hy : 0≤v:= q.exponent_pos.le.trans Y.wide
  have H₁ := pledges hb hp hq Y.squeeze hy
  let U:= vacancies v Λ σ C δ b p q
  let s:=2*U+ plane w v+batch u (v+1) q.B
  obtain ⟨W,hW,hV,ht⟩:=Volunteer.winds H₁ (add_nonneg hy zero_le_one) Y.entitled
  let X:=signal Z hp hv.good hv.size q.threshold_pos he b (n:=n)
  have he':= humid Z p q hp hv.good hv.size he hb (add_nonneg hy zero_le_one) u hv.tight Y.hale (n:=n)
  let F:=orig A p hq.forced
  have hU (U:Config G n) : Summable (fun i=> placed F i U) := by
    refine ((Activities.gasSeries hq).summable U).congr fun i=> gas_at ..
  obtain ⟨R,hR,HM,hs,hM,h⟩:= accommodate F (old_hymn hq) (old_cost hq) P.p.exponent_pos.le hU
  have hL (x : Config G n) : A.gas p x = ∑ i, placed R i x:= by
    rw [h]; apply tsum_congr; intro i; exact gas_at ..
  let f : Empty → Site n:= Empty.elim; let T := enroll f∘R
  let r (_ : Empty):ℝ:= 1
  have hr : Burden T q r (v+1) (plane w v):= by
    obtain ⟨i,h,hs⟩:= hs; have h1 : scalesExp p q (v+1) := by
      refine le_trans ?_ Y.squeeze.2.1;show _≤100000*(p.B:ℝ)*(v+2);gcongr; linarith
    refine ⟨i, fun j=> ⟨(h j).1,fun x=>?_⟩,ShiftUp (E:=T) _ _ hv _ (add_nonneg hy zero_le_one) h1 (fun i=> (h i).1) _ hs⟩
    change Poly.toll r (quiet Empty)*‖(↑((R j).value x):ℂ)‖≤_; simp only [Poly.toll,quiet,Census.quiet, Finset.prod_empty,one_mul,Complex.norm_real]; exact (h j).2 x
  have hF:=Y.site s rfl
  have hn₁ : 0≤2*U:= by
    obtain ⟨c,h,H⟩:=hV; have hp:= H 0; exact (tsum_nonneg hp.1).trans hp.2.2
  have hn : 0≤s:= by
    obtain ⟨_,_,Hp⟩:=hr; obtain ⟨_,_,Hg⟩:=he'; have Hx:=Hp 0; have Hy:=Hg 0
    exact add_nonneg (add_nonneg hn₁ ((tsum_nonneg Hx.1).trans Hx.2.2)) ((tsum_nonneg Hy.1).trans Hy.2.2)
  obtain ⟨B,h1,h2,h3,hBg,h4⟩:=regal f HM hW (show Peace X from systematic Z hp hv.good hv.size q.threshold_pos he b) hv.good (fun i=>zero_lt_one) hV hr he' hF.2 le_rfl hy Y.cost hn
  have hP:= SumHit.raised h3 Y.wide
  haveI : Nonempty (Neat n) := ⟨⟨({0},{0}),singleton_nonempty _,subset_refl _⟩⟩
  obtain ⟨E⟩:= (show Nonempty (Equiv ℕ ((Neat n)×ℕ)) by infer_instance)
  let T:= lengthen A q B E
  let Q: Rep G n:={ activities:=T,p:=q,path:=Z,v:=P.v,beta:=b,clip:=C' }
  have ha:T.Valid q δ (Real.exp (-u)):= by
    have hz:=lengthy q B h1 E A hP
    refine ⟨?_,plenty q B h1 E A,presented q hq.moves E h1 h2,thinner hv hq.boundE,?_⟩
    · have hH := hv.untouched hq.regular; exact ⟨hH.smooth,hH.at_flat,hH.vanish⟩
    obtain ⟨c,hc,hz⟩:=hz; refine ⟨c,hc,fun x=>⟨(hz x).1,(hz x).2.1,le_trans ((hz x).2.2) ?_⟩⟩
    have hv':|Real.exp s-1|≤2*|s|:=Real.abs_exp_sub_one_le (by rw [abs_of_nonneg hn]; linarith only [hF.1])
    rw [abs_of_nonneg hn] at hv'; exact mul_le_of_le_one_right (Real.exp_pos _).le (by linarith only [hF.1,(abs_le.mp hv').2])
  have hh (x) : Real.exp (P.exponent x)=Real.exp (Q.exponent x)*(∏ i,((W i).value x+1))*∏ i∈flags q.threshold x,X.value i x:= by
    rw [pours _ hp hv.good hv.size q.threshold_pos he, ← ht,← Real.exp_add,← Real.exp_add]; apply congr_arg Real.exp
    -- same E
    have heq : T.additive q x=A.additive q x:= rfl
    unfold Rep.exponent loose
    rw [show Q.activities.additive Q.p x=A.additive q x from heq]; dsimp only [Z,X,Q,T,b,A,p,C',eng, rupture]; ring
  refine ⟨X,W,Q,⟨⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩, systematic Z hp hv.good hv.size q.threshold_pos he b, he', hW,hV,hh,?_⟩,funext fun x=> ?_,H.paths,ha⟩
  · intro R' hr he i U W'
    have hx : R'=R:= uniqueR hr hR he hM
    subst R'; rw [show Archive Q.activities i U = _ from longest A B E i U]; exact hBg i U
  change Real.exp _*T.gas q x=Real.exp (P.exponent x)*A.gas p x; rw [stretcher q B h1 E A ha x, h4,hh,hL]; ring
end YM.Next.Rank.Alarm
