import YM.RG08.Shade.Operas
import YM.RG08.Wallet.Stays
/-!
# Resolve winding variant of formal mark numerator. Qualitative, every grid test
meets exact series Ward after this limit. Quantitative cutoff limit distinct.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Quire
open Function Filter Lattice Wilson Exterior Bloch Next.Free Work.F08 RG Laurent Precision Finset
open Quire Stationary Matrix Push.AbsoluteSums Shade
open scoped Topology ContDiff Classical BigOperators
variable {E F α β γ ι : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {L m r n k s : ℕ}
structure Decline (x : ℕ→Rooted E α r) : Prop where
    thus : ∃ f : ℕ→ℝ,Tendsto f atTop (𝓝 0) ∧ ∀ i,Lit (x i) 0 (f i)
structure Hurled (x : ℕ→Rooted E α r) (f : Rooted E α r) : Prop where
    old : Pens f
    moment : Decline (fun i=> x i-f)
variable {x y : ℕ→Rooted E α r} {f g : Rooted E α r}
lemma Pens.black (h : Pens f) : Lit f 0 (∑' i,‖f i‖) := by
  rw [Quire.Lit,show (ling 0:Beads α r→ℝ)=1 from funext fun i=>by simp [ling]]; exact h.priced
lemma Decline.zero : Decline (0:ℕ→ Rooted E α r) := ⟨_,tendsto_const_nhds (x:= (0:ℝ)),fun i=> Ink.none ..⟩
lemma Decline.plus (h : Decline x) (hp : Decline y) : Decline (x+y) := by
  obtain ⟨a,ha,ht⟩:=h.thus; obtain ⟨b,hB,H⟩:=hp.thus; exact ⟨_, (zero_add (0:ℝ) ▸ ha.add hB),fun i=> Ink.plus (ht i) (H i) (fun j=> (ling_one le_rfl j).trans' zero_le_one)⟩
lemma Decline.atCost (h : Decline x) (t : ℝ) : Decline (t • x) := by
  obtain ⟨a,ha,H⟩:=h.thus; exact ⟨fun i=> ‖t‖*a i,by simpa using ha.const_mul ‖t‖,fun i=> Ink.scale (H i) t⟩
lemma Decline.pens (h : Decline x)(i): Pens (x i) := (h.thus.choose_spec.2 i).pens (ling_one le_rfl)
lemma Hurled.ever (h : Hurled x f)(i) : Pens (x i) := by simpa using (show Pens (x i-f+f) from (h.moment.pens i).plus h.old)
lemma Hurled.plus (h : Hurled x f) (ht : Hurled y g) : Hurled (x+y) (f+g) := by
  refine ⟨h.old.plus ht.old,?_⟩; convert h.moment.plus ht.moment using 1; funext i; simp only [Pi.add_apply]; abel
lemma Hurled.scale (h : Hurled x f) (t : ℝ) : Hurled (t • x) (t • f) := by
  refine ⟨h.old.scale _,?_⟩; convert h.moment.atCost t using 1; funext i; simp only [Pi.smul_apply,smul_sub]
lemma Hurled.fixed (h : Pens f) : Hurled (fun _=>f) f := ⟨h,by simp only [sub_self]; exact Decline.zero⟩
lemma Hurled.additions (s : Finset ι){x : ι→ℕ→Rooted E α r} {f : ι→Rooted E α r} (h : ∀ i∈s, Hurled (x i) (f i)) : Hurled (fun j=>∑ i∈s,x i j) (∑ i∈s,f i) := by
  induction s using Finset.induction_on with
  | empty=> simp only [sum_empty]; exact Hurled.fixed (Pens.zero ..)
  | insert i s hi ih=> simp_rw [sum_insert hi]; exact (h _ (mem_insert_self ..)).plus (ih (fun v hv=> h v (mem_insert_of_mem hv)))

section payments
variable {P : Row α α} (m : ℕ→Side)
lemma knot_unwind {f : Rooted E α (r+2)}(h : Pens f)(ht : Tendsto (fun i=>(m i).val) atTop atTop)(he : Whole P): Hurled (fun i=> jib (some (m i)) P f) (jib none P f) := by
  let s (i : ℕ) (p:Beads α (r+2)) := knot (some (m i)) f P p - knot none f P p
  have hy (i): s i= _ := (rfl:s i=knot (some (m i)) f P-knot none f P)
  have hh i : Pens (s i) := (knot_prices h he _).less (knot_prices h he _)
  let a i:= ∑' j, ‖s i j‖
  have hS : Tendsto a atTop (𝓝 0) := by
    obtain ⟨σ,C,hσ,H⟩:=he -- local
    have hz p : Tendsto (fun i=> ‖s i p‖) atTop (𝓝 0) := by
      have hD : Tendsto (fun i=> tuneS P (some (m i)) p) atTop (𝓝 (tuneS P none p)) := stroke_late P (Whole.safe (A:=P) ⟨_,_,hσ,H⟩) m ht .. -- safe arg
      simpa using! ((hD.smul_const (f p)).sub_const (tuneS P none p • f p)).norm
    have hx (i j): ‖s i j‖≤ (2*C)*‖f j‖ := by
      have hr p : ‖knot p f P j‖≤ C*‖f j‖ := by unfold knot; rw [norm_smul]; exact mul_le_mul_of_nonneg_right (stroke_known _ H hσ.le _ _ _) (norm_nonneg _)
      exact (norm_sub_le ..).trans ((add_le_add (hr _) (hr _)).trans_eq (by ring))
    simpa using! tendsto_tsum_of_dominated_convergence (h.mul_left (2*C)) hz (.of_forall (fun i j=> by simpa only [norm_norm] using hx i j))
  constructor
  · exact (jib_tidy h he _).pens
  refine ⟨_,(show Tendsto (fun i=> ‖batting r‖*a i) atTop (𝓝 0) from by simpa using hS.const_mul ‖batting r‖),fun i=>?_⟩
  unfold jib; rw [← sew_sub, ← smul_sub, ← Pens.tub_sub stems (knot_prices h he _) (knot_prices h he _)]
  refine stitching (Ink.scale (Ink.pour stems ?_ (ling_one le_rfl)) (batting r))
  rw [show ling 0 ∘ (stems (α:=α) (r:=r))=1 from funext fun i=>by simp [ling]]; exact (hh i).priced
lemma Hurled.jib_l {F : ℕ→Rooted E α (r+2)} {f : Rooted E α (r+2)}(ht : Hurled F f)(hp : Whole P)(h : Tendsto (fun i=>(m i).val) atTop atTop): Hurled (fun i=>jib (some (m i)) P (F i)) (jib none P f) := by
  let q i:=jib (some (m i)) P (F i-f); have hh:= knot_unwind m ht.old h hp
  have hc: Decline q := by
    obtain ⟨δ,hδ,H⟩:= ht.moment.thus; obtain ⟨σ,C,hσ,hQ⟩:=hp; refine ⟨fun i=> ‖batting r‖*((max 0 C)*δ i),by simpa using! (hδ.const_mul _|>.const_mul _),fun i=> jib_print (H i) le_rfl (strip_mono hQ le_rfl (le_max_right 0 C)) hσ.le (le_max_left ..) _⟩ -- order product B*A
  refine ⟨hh.old,?_⟩; convert hc.plus hh.moment using 1; funext i; simp only [Pi.add_apply,q,jib_less _ (ht.ever i) ht.old hp,sub_add_sub_cancel]

lemma Hurled.clasp_l {U : ℕ→Rooted E α (r+1)} {H : ℕ→Shale α (s+1)} {u v} (h : Hurled U u) (he : Mending H v) (hp : Whole P) : Hurled (fun i=>clasp P (U i) (H i)) (clasp P u v) := by
  have hh:=clasp_tidy h.old he.1.summable hp
  let T i:= U i-u; let a i:= H i-v
  let b i:=clasp P (T i) (H i); let c i:=clasp P u (a i)
  have hx : (fun i=> clasp P (U i) (H i)- clasp P u v)=b+c := funext fun i=> by unfold b c T a; rw [Pi.add_apply,clasp_balance (h.ever i) h.old (he.ever i|>.summable) hp,clasp_income h.old (he.ever i|>.summable) he.1.summable hp]; abel
  refine ⟨hh.pens,hx ▸ Decline.plus ?_ ?_⟩
  · obtain ⟨d,hd,hz⟩:= h.moment.thus; obtain ⟨w,C,hC,HW⟩:= he.bounds -- requires Fintype
    obtain ⟨t,B,ht,Ht⟩:= hp
    refine ⟨fun i=> ‖syl r s‖*(max 0 B*(d i*C)),by simpa using! (((hd.mul_const C).const_mul (max 0 B)).const_mul ‖syl r s‖),fun i=> clasp_cost le_rfl (by simpa only [mul_zero] using hz i) (glow_less (HW i) hC.le le_rfl) (strip_mono Ht (by rw [mul_zero]; exact ht.le) (le_max_right ..)) (le_max_left ..)⟩
  obtain ⟨t,B,ht,Ht⟩:=hp; obtain ⟨w,d,hd,hδ,Hd⟩:=he.2
  let S':= ∑' j,‖u j‖
  exact ⟨fun i=> ‖syl r s‖*(max 0 B*(S'*d i)),by simpa using! (((hδ.const_mul S').const_mul (max 0 B)).const_mul ‖syl r s‖),fun i=>clasp_cost le_rfl (by rw [mul_zero]; exact h.old.black) (glow_less (Hd i) hd.le le_rfl) (strip_mono Ht (by rw [mul_zero]; exact ht.le) (le_max_right ..)) (le_max_left ..)⟩
lemma Hurled.granting (h : Hurled x f) (k): Hurled (fun i=> grant k (x i)) (grant k f) := by unfold grant; split_ifs with he; subst k; exact h; exact Hurled.fixed (Pens.zero ..)
variable [Fintype α]
lemma Hurled.furs {U : ℕ→Screed E α}{S : Screed E α}{T : Canticle α} (h : ∀ i j,Hurled (fun v=> U v i j) (S i j))(he : Gets T)(hP : Whole P) (hp : Tendsto (fun i=>(m i).val) atTop atTop) : Hurled (fun i=>murmur (some (m i)) P T (U i) n k r) (murmur none P T S n k r) := by
  induction n using Nat.caseStrongRecOn generalizing k r with
  | zero=> simp_rw [murmur]; exact h k r
  | ind n ih=>
    simp_rw [murmur_step]; apply Hurled.scale (x:=fun i=> _+_)
    refine Hurled.plus (x:=fun i=>jib (some (m i)) P _) ((ih n le_rfl).jib_l m hP hp) ?_
    let F (b a:ℕ×ℕ)(i) := hymn P (murmur (some (m i)) P T (U i) b.1 a.1) (Refrain P T (some (m i)) b.2 a.2) r
    let V (b a:ℕ×ℕ) := hymn P (murmur none P T S b.1 a.1) (Refrain P T none b.2 a.2) r
    refine Hurled.additions (wheel n) (x:=fun j i=> ∑ b∈wheel k,F j b i) (f:=fun j=>∑ b∈wheel k,V j b) (fun b hb=>Hurled.additions (x:=F b) (f:=V b) (wheel k) (fun a _=>?_))
    unfold F V hymn; exact Hurled.additions (wheel r) fun c hc=> Hurled.granting ((ih b.1 (by have hg:=mem_antidiagonal.mp hb; omega) (k:=a.1)).clasp_l (Mending.both (fun i j=> Mending.one (T i j) (he.2 i j|>.2)) hP hp b.2 a.2 _) hP) r
lemma WashHurled {U : ℕ→ Screed E α} {u S} (h : ∀ i j,Hurled (fun v=> U v i j) (u i j))(he : Gets S)(hP : Whole P) (hp : Tendsto (fun i=>(m i).val) atTop atTop) : Hurled (fun i=> washed L (some (m i)) P S (U i) k r) (washed L none P S u k r) :=
    Hurled.additions (range (windows L k+1)) (fun _ _=> Hurled.furs m h he hP hp)

variable [Fintype β] {M : Row α β}
lemma Hurled.spring (h : Hurled x f)(hp : Whole M) : Hurled (fun i=> Shade.spring (x i) M) (Shade.spring f M) := by
  refine ⟨(spring_tidy h.old hp).pens,?_⟩
  simp_rw [← spring_sub (h.ever _) h.old hp]
  obtain ⟨d,hd,Hd⟩:=h.moment.thus; obtain ⟨w,B,hw,H⟩:=hp
  exact ⟨_,(show Tendsto (fun i=>(↑(Fintype.card β)^r*(max 0 B)^r)*d i) atTop (𝓝 0) from by simpa using hd.const_mul _),fun i=> spring_receipt (Hd i) le_rfl (le_max_left ..) (strip_mono H hw.le (le_max_right 0 B))⟩
lemma Hurled.maps (h : Hurled x f)(g : E→L[ℝ] F) : Hurled (fun i=> g ∘ x i) (g ∘ f) := by
  refine ⟨h.old.shaped g,?_⟩; obtain ⟨q,hq,H⟩:=h.moment.thus; refine ⟨fun j=> ‖g‖*q j,by simpa using hq.const_mul ‖g‖,fun i=> ?_⟩
  change Lit ((g ∘ x i) - (g ∘ f)) 0 _; rw [show (g∘x i)-(g∘f) = g∘(x i-f) from funext fun i=> (map_sub ..).symm]; exact Ink.some (H i) g (fun i=>(ling_pos _ _).le)
end payments
end YM.RG08.Quire
