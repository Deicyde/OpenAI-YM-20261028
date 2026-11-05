import YM.RG08.Wax.Atlas
/-! # Root ages. Hold every specific marker and all transverse field paths.
 Coordinate absolute field positions on Cover. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Wax
open Function Filter RG Lattice Laurent Stationary Quire Analysis Shade Vale Bands Loom Next.Free Bloch Scores Finset Push.AbsoluteSums UVExt.Paths Town
open scoped Topology BigOperators Real Classical
variable {I E X Z:Type} [DecidableEq I] [NormedAddCommGroup E] {i j k r s D:ℕ}{A B w v:ℝ}{W: Finset I}
-- layout coherence uses outside T anywhere
abbrev Places (I:Type):= I→Cover
abbrev Fleet (W:Finset I):= W→ Cover

def pin (W:Finset I)(x:Places I): Fleet W:= fun i=> x i.val
def loose (W:Finset I)(x:Fleet W): Places I:= fun i=> if h:i∈W then x ⟨i,h⟩ else 0
lemma pin_loose (W:Finset I)(x:Fleet W): pin W (loose W x)=x:= funext fun i=> dif_pos i.property
def Only (W:Finset I)(F:Places I → X): Prop:= ∀ x y, (∀ i∈W,x i=y i) → F x=F y
lemma only_pin {F:Places I→X}(hp:Only W F)(x:Places I): F x=F (loose W (pin W x)):= hp _ _ fun i hi=>(show loose W (pin W x) i=x i from dif_pos hi).symm
lemma Only.comp {F:Places I→X} (h: Only W F)(G:X→E): Only W (G∘F):= fun p q hp=> congr_arg G (h p q hp)
lemma Only.out {F:Places I→ X} {T:Finset I}(h:Only W F)(he:W⊆T): Only T F:= fun x y hp=> h x y fun i hi=> hp i (he hi)
lemma Only.sumOnly {f : Z→Places I→E}(s:Finset Z)(h:∀ i∈s, Only W (f i)): Only W (fun x=>∑ i∈s,f i x):=fun x y hv=> sum_congr rfl fun i hi=> h i hi x y hv
-- absolute proof no test movement

def stretch (z:Cover)(p:Beads X r) := ∑ i,size ((p i).1-z)
def pale (z:Cover)(w:ℝ)(p:Beads X r):= Real.exp (w*stretch z p)
abbrev Pail (z:Cover)(w:ℝ)(f:Rooted E X r)(C:ℝ) := Ink (pale z w) f C
def Mounts (a:W)(p:Fleet W) := ∑ i : W,size (p i-p a)
def Tribe (a:W)(p:Fleet W)(w:ℝ) (A:ℝ):= Real.exp (w*Mounts a p)*A
abbrev Held (a:W)(x:Cover):= {p:Fleet W // p a=x}
-- not summing translation origin even on mark∅ applied external. costs only claimed for nonempty marker sets
def Owns (w:ℝ)(W:Finset I)(F:Places I→Rooted E X r)(C:ℝ): Prop:=
    Only W F ∧ 0≤C ∧ ∀ a:W,∃ U:Fleet W→ℝ,(∀ p,Pail (p a) w (F (loose W p)) (U p)) ∧ ∀ x, SumBudget (fun i: Held a x=> Tribe a i.val w (U i.val)) C
lemma Owns.pos {F:Places I→Rooted E X r}(h:Owns v W F A): 0≤A := h.2.1
lemma pale_one (x:Cover)(hp:0≤w): 1 ≤ (pale (r:=r) (X:=X) x w):= fun _=>Real.one_le_exp (mul_nonneg hp (Nat.cast_nonneg _))
lemma owns_none (W:Finset I)(w:ℝ)(hp:0≤A)(X E : Type)[NormedAddCommGroup E](r:ℕ): Owns w W (fun _=> (0:Rooted E X r)) A:= by
    refine ⟨fun _ _ _=>rfl,hp,fun a=>⟨0,fun i=>Ink.none _ E,fun x=>?_⟩⟩; simp only [Tribe,Pi.zero_apply,mul_zero]; exact budget_loosen (by exact (Ink.none (fun _:Held a x=>1) E) |> fun h=> by simpa [Quire.Ink] using h) hp
variable {F G:Places I→ Rooted E X r}
lemma owns_plus (h:Owns w W F A)(hp:Owns w W G B) : Owns w W (F+G) (A+B) := by
   refine ⟨fun x y hv=> congr_arg₂ (·+·) (h.1 x y hv) (hp.1 x y hv),add_nonneg h.pos hp.pos,fun i=>?_⟩
   obtain ⟨f,H,hr⟩:= h.2.2 i; obtain ⟨g,P,hg⟩:=hp.2.2 i; refine ⟨f+g,fun p=> Ink.plus (H p) (P p) (fun i=> (Real.exp_pos _).le),fun p=>?_⟩
   simpa only [Tribe,Pi.add_apply,mul_add] using budget_plus (hr p) (hg p)
lemma owns_sum {U:Z→Places I→Rooted E X r} {P:Z→ℝ}(t:Finset Z)(hp:∀ i∈t,Owns w W (U i) (P i)): Owns w W (fun z=>∑ i∈t,U i z) (∑ i∈t,P i):=by
  induction t using Finset.induction_on with
  | empty=> simp only [sum_empty]; exact owns_none W w le_rfl ..
  | insert i s hi ih=> simp_rw [sum_insert hi]; exact owns_plus (hp _ (mem_insert_self ..)) (ih fun i h=> hp i (mem_insert_of_mem h))
lemma owns_mono (h:Owns w W F A)(hv:v≤w)(hp:A≤B): Owns v W F B:= by
  refine ⟨h.1,h.pos.trans hp,fun i=>?_⟩
  obtain ⟨U,hw,h⟩:=h.2.2 i
  refine ⟨U,fun j=> Ink.shrink (hw j) (fun x=> (Real.exp_pos _).le) (fun x=> Real.exp_monotone (mul_le_mul_of_nonneg_right hv (by positivity))),fun x=>?_⟩
  exact budget_loosen (budget_mono (h x) (fun x=>mul_nonneg ((Real.exp_pos _).le) (Ink.nonneg (hw _))) fun x=>mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_right hv (by positivity))) (Ink.nonneg (hw _))) hp
variable [NormedSpace ℝ E]
lemma owns_s (h:Owns w W F A)(r:ℝ): Owns w W (r • F) (‖r‖ * A) := by
    refine ⟨fun x y hp=>congr_arg (r • ·) (h.1 x y hp),mul_nonneg (norm_nonneg _) h.pos,fun a=>?_⟩; obtain ⟨U,hu,he⟩:=h.2.2 a
    refine ⟨fun p=>‖r‖*U p,fun p=>(hu p).scale _,fun p=> ?_⟩; simpa only [Tribe,mul_left_comm ‖r‖] using budget_scale (norm_nonneg r) (he p)
-- all marks equal contribution operations linear per root
variable {Z:Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
lemma owns_tilt (h:Owns w W F A)(hp:v ≤ w)(he:0 ≤ B) (op:Rooted E X r → Rooted Z X s)
    (H:∀ (U:Rooted E X r) (a:Cover) (C:ℝ),Pail a w U C→ Pail a v (op U) (B*C)): Owns v W (op ∘ F) (B*A) := by
   refine ⟨fun x y hp=> congr_arg op (h.1 x y hp),mul_nonneg he h.pos,fun i=>?_⟩; obtain ⟨U,hp',hx⟩:=h.2.2 i
   refine ⟨_,fun k=> H _ _ _ (hp' k),fun x=>?_⟩; apply budget_mono (budget_scale he (hx x)) (fun _=> mul_nonneg (Real.exp_pos _|>.le) (Ink.nonneg (H _ _ _ (hp' _))))
   intro z; unfold Tribe; rw [mul_left_comm]; gcongr
   exact Ink.nonneg (hp' _)
end YM.RG08.Wax
