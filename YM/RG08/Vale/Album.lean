import YM.RG08.Vale.Ladle
import YM.RG08.Vale.Verse
/-!
# The normalized *formal* projection onto SectionData coordinates
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Vale
open RG Laurent Lattice Wilson Bloch Exterior Push.AbsoluteSums Finset Function Filter
open UVExt.Paths Stationary Planned.PrimaryIntegral295 Shade Quire Source Source.Drops Labels Scores Tall
open scoped Topology ContDiff Classical BigOperators
variable {I E α:Type} {G:Gauge} {d D i j k r n τ u m e : ℕ} {R:ℝ} {F : Labels.Frame G d}
variable {V W: BoardU D R G} {X : Screed E α} [NormedAddCommGroup E]
def Lank (U:Screed E α) := ∀ e r,Polished (U e r)
lemma lank_zero : Lank (0:Screed E α) := fun e r=> polished_zero _ _ _
lemma lank_add {Y:Screed E α} (h:Lank X)(hp:Lank Y) : Lank (X+Y) := fun k r=> polished_more (h k r) (hp k r)
lemma lank_wt [NormedSpace ℝ E](h:Lank X)(p:ℝ) : Lank (p • X) := fun i j=> polished_scale (h i j) p
lemma lank_tbl {X:I→Screed E α} {s:Finset I}(h:∀ i∈s,Lank (X i)): Lank (∑ i∈s,X i) := by
  induction s using Finset.induction_on with
  | empty=>rw [sum_empty]; exact lank_zero
  | insert i s hi ih=>rw [sum_insert hi]; exact lank_add (h _ (mem_insert_self ..)) (ih fun j hj=> h _ (mem_insert_of_mem hj))
lemma lank_fee [NormedSpace ℝ E][CompleteSpace E] (h:Lank X)(m:ℕ): Lank (fem m X) := by
  intro i j; unfold fem; split; exact h _ _; exact polished_zero E _ _
structure Letter (F:Labels.Frame G d) where
  label : F.Index
  test : Cham
  bill : (F.grades label).1+cashT test ≤ d

def fee {F:Labels.Frame G d}(i:Letter F) := (F.grades i.label).1 + cashT i.test
def slot {F:Labels.Frame G d}(i:Letter F) := (F.grades i.label).2
lemma slot_le {F:Labels.Frame G d}(i:Letter F) : slot i ≤ d := Film.second_fits F i.label
instance let_fin : Fintype (Letter F) := by
  refine @Fintype.ofFinite (Letter F) ?_
  let f(p:Letter F) : F.Index × ↥(rangeT d) := (p.label, ⟨p.test,(counted _).2 (le_trans (Nat.le_add_left ..) p.bill)⟩)
  refine Finite.of_injective f ?_
  rintro ⟨i,a,h⟩ ⟨j,b,v⟩ hF; simpa [f,Subtype.ext_iff] using hF
instance let_De : DecidableEq (Letter F) := Classical.decEq _

abbrev Band (F:Labels.Frame G d) := Letter F→ℝ
abbrev Beam (F:Labels.Frame G d) := ℕ→ Band F

def graceT (H:Hol G)(V:EnvelopeU D R G r)(φ: Exam D) (i:F.Index): ℂ := F.coords (ladle H (plug φ R ∘ V) d (F.grades i).2) i
def invest (H:Hol G)(V : EnvelopeU D R G r)(i:Letter F) : ℝ := (graceT H V (coinsT D i.test) i.label).re
-- e+r≥slot output for earned candidate
def auditT (H:Hol G)(F:Labels.Frame G d)(U:BoardU D R G): Beam F :=
    fun e b=> ∑ r∈range (slot b+1), if slot b ≤ e+r then invest H (U (e+r-slot b) r) b else 0
-- useful linearity/prices
variable (H:Hol G) {P : KernelChoices}
lemma inserted (i:Letter F)(j:EnvelopeU D R G r): ((invest H j i :ℝ):ℂ) = graceT H j (coinsT D i.test) i.label := ladle_real ..
lemma shaped_d (h:Marvel τ V) (g : Exam D) : Dappled (plug g R ∘ V i r) := costed_dapple (U:=fun i j=> plug g R ∘ V i j) (fun i j=> Tidy.map _ (h.hem i j)) (fun m=> h.wardrobe m g 0) (Fits.echo h.cap g)
lemma invest_paid {Φ:EnvelopeU D R G r} (b : Letter F)(h:slot b < r) : invest H Φ b=0 := by unfold invest graceT;unfold slot at h; rw [ladle_arity H h,map_zero]; rfl
@[simp] lemma invest_zero (b:Letter F) : invest H (0:EnvelopeU D R G r) b=0 := by
  unfold invest graceT; rw [show plug (coinsT D b.test) R ∘ (0:EnvelopeU D R G r)= (0:Shale (Loc G 1) r) from funext fun i=>map_zero _,ladle_zero, map_zero]; rfl
lemma invest_plus (q:Letter F) (hV:Marvel τ V) (hH:Marvel u W) (hv:Lank V)(hW:Lank W) : invest H ((V+W) k r) q=invest H (V k r) q+invest H (W k r) q := by
  unfold invest graceT; rw [show plug (coinsT D q.test) R ∘ (V+W) k r=(plug (coinsT D q.test) R∘ V k r)+(plug (coinsT D q.test) R∘ W k r) from funext fun _=>map_add .., ladle_add H (shaped_d hV _) (shaped_d hH _) (polished_fun (hv k r) _) (polished_fun (hW k r) _),map_add]; rfl
lemma invest_wt (q:Letter F)(t:ℝ)(h:Marvel τ V)(hv:Lank V): invest H ((t•V) k r) q=t*invest H (V k r) q := by
  unfold invest graceT; rw [show plug (coinsT D q.test) R ∘ (t•V) k r=t • (plug (coinsT D q.test) R∘V k r) from funext fun i=>by simp,ladle_scale H (shaped_d h _) (polished_fun (hv k r) _),map_smul]; simp only [Pi.smul_apply,smul_eq_mul, Complex.re_ofReal_mul]
lemma audit_plus (h:Marvel τ V) (g:Marvel u W) (hv:Lank V)(hp:Lank W): auditT H F (V+W)=auditT H F V+auditT H F W := by
  funext e b; change _=auditT _ _ V e b+auditT _ _ W e b; unfold auditT
  rw [←sum_add_distrib]; refine sum_congr rfl fun j _=>?_; split_ifs; exact invest_plus H b h g hv hp; rw [add_zero]
lemma audit_scale (c:ℝ)(h:Marvel τ V)(he:Lank V): auditT H F (c•V)=c • auditT H F V := by
  ext1 e; ext b
  unfold auditT; rw [Pi.smul_apply,Pi.smul_apply,smul_eq_mul,mul_sum]
  apply sum_congr rfl; intro r hr; split_ifs; exact invest_wt H b _ h he; simp
lemma audit_zero : auditT H F (0:BoardU D R G)=0 := by ext n b; simp [auditT]
lemma audit_sub (h:Marvel τ V)(g:Marvel u W)(he:Lank V)(hp:Lank W): auditT H F (V-W)= auditT H F V-auditT H F W := by rw [sub_eq_add_neg,← neg_one_smul ℝ W,audit_plus H h (choir_weight g _) he (lank_wt hp _),audit_scale H _ g hp,neg_one_smul,sub_eq_add_neg]
lemma audit_sums {s:Finset I}{v:I→BoardU D R G}(h : ∀ i∈s,Marvel τ (v i))(p:∀ i∈s,Lank (v i)): auditT H F (∑ i∈s,v i)=∑ i∈s,auditT H F (v i) := by
  induction s using Finset.induction_on with
  | empty=>rw [sum_empty,audit_zero,sum_empty]
  | insert i s hi ih=>
    have hx (j) (hj:j∈s):= p _ (mem_insert_of_mem hj); have hy (j) (hj:j∈s):=h _ (mem_insert_of_mem hj)
    rw [sum_insert hi, sum_insert hi, audit_plus H (h _ (mem_insert_self ..)) (choir_array s hy) (p _ (mem_insert_self ..)) (lank_tbl hx), ih hy hx]
lemma audit_fee (V:BoardU D R G)(u e:ℕ)(v:Letter F) : auditT H F (fem u V) e v= if u≤e then auditT H F V (e-u) v else 0 := by
  rcases le_or_gt u e with hp|hp
  · rw [if_pos hp]; apply sum_congr rfl; intro r hr
    split_ifs with h g
    · rw [footing (by omega),show e+r-slot v-u=e-u+r-slot v by omega]
    · unfold fem; rw [if_neg (by omega),invest_zero]
    all_goals first|omega|rfl
  rw [if_neg (not_le.mpr hp)]; refine sum_eq_zero fun i hi=> ?_; have hh:=mem_range.mp hi
  split; next h=> unfold fem; rw [if_neg (by omega),invest_zero]
  next h=> rfl
lemma audit_cap (h: Fits τ V) (b:Letter F) (hp: e+τ < slot b) : auditT H F V e b=0 := by
  refine sum_eq_zero fun i hi=>?_ ; split
  next he=> rw [show V _ i=0 from not_ne_iff.mp (mt (h _ i) (by omega)), invest_zero]
  next he=> rfl

lemma invest_price (u : Letter F) (R:ℝ) (r D:ℕ): ∃ A:ℝ, 0≤A ∧ ∀ (V: EnvelopeU D R G r) (C:ℝ), Quire.Ink (mint (d*slot u)) V C → ∀ H:Hol G,‖invest H V u‖≤ A*C := by
  obtain ⟨A,hA,h⟩:= ladles G F (slot u) r; let a:= plug (coinsT D u.test) R
  let t:=‖a‖; have ht:0≤t:= norm_nonneg a
  refine ⟨A*t,mul_nonneg hA ht,fun V C hp H=>?_⟩
  have he : Ink (mint (d*slot u)) (a ∘ V) (t*C) := hp.some a (mint_pos _ _ _)
  rw [← Complex.norm_real,inserted]; exact ((norm_le_pi_norm (F.coords (ladle H (a ∘ V) d (slot u))) u.label).trans (h _ _ he H)).trans_eq (mul_assoc ..).symm

-- horizon capture through grade E uses exactly same projections across cutoffs
lemma strandP (h:Lank V) (φ:Exam D) : Polished (Loom.strand τ i (fun j k=> plug φ R∘V j k) r) := by
  unfold Loom.strand; split; apply polished_fun (h _ _); exact polished_zero ℝ _ _
lemma audit_tile (h:Marvel τ V) (p:Lank V)(b:Letter F) :
    F.coords (∑ j∈range (slot b+1), ladle H (Loom.strand τ i (fun e r=>plug (coinsT D b.test) R∘ V e r) j) d (slot b)) b.label =
      if τ≤ i+slot b then ↑(auditT H F V (i+slot b-τ) b) else 0 := by
  rw [map_sum,Finset.sum_apply]
  split; next hp=>
    unfold auditT; push_cast; refine sum_congr rfl fun j _=>?_; unfold Loom.strand; split_ifs <;> first
       | rw [ladle_zero,map_zero]; rfl
       | omega
       | rw [inserted,show i+slot b-τ+j-slot b=i+j-τ by omega]; rfl
  next hp=>
    refine sum_eq_zero fun j hj=> ?_; unfold Loom.strand; rw [if_neg (by have ht:=mem_range.mp hj; omega),ladle_zero,map_zero]; rfl
end YM.RG08.Vale
