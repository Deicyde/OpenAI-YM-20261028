import YM.RG08.Wax.Mingle
/-! # Mincer. Pair wages, including polymer metric anchored at any
persistent tag. No ℓ∞ probe assumption.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Wax
open Function Filter RG Lattice Laurent Stationary Quire Analysis Shade Vale Bands Loom Next.Free Bloch Scores Finset Push.AbsoluteSums UVExt.Paths Town Work.F08
open scoped Topology BigOperators Real Classical
variable {I E X Z Y:Type} [Fintype I] [DecidableEq I] [NormedAddCommGroup E] [NormedAddCommGroup Y][NormedAddCommGroup Z] {i j k r s n t d D:ℕ}{A B w v K θ R:ℝ}{U V T:Finset I}
-- generic ep. H : any Bilin. only left orientation
lemma we_go (ht:T=U∪V)(h:Disjoint U V)(hs:V.Nonempty)(hv:0<v)(hw:v≤w)(hk:V.card ≤ k)(hK:0≤K)
    {F:Places I→Rooted E X r}{G:Places I→Rooted Z X s}{H:Places I→Rooted Y X n}(ha:Owns w U F A)(hg:Owns w V G B)
    (hc : ∀ (x:Places I)(i j: Cover) (u v' : ℝ), Pail i w (F x) u → Pail j w (G x) v' → Pail i v (H x) (Real.exp (-((k+1:ℕ)*v)*size (i-j))*K*(u*v')))
    (a:T)(hp:a.val∈U): ∃ p:Fleet T→ℝ, (∀ b, Pail (b a) v (H (loose T b)) (p b)) ∧ ∀ x,SumBudget (fun i:Held a x=> Tribe a i.val v (p i.val)) (K*(A*(B*shells v))) := by
    let b:U:=⟨a,hp⟩; obtain ⟨c,hc'⟩:=hs; let j:V:=⟨c,hc'⟩
    obtain ⟨F',hF,hP⟩:=ha.2.2 b; obtain ⟨G',hG,hM⟩:=hg.2.2 j
    let u p:=pin U (loose T p); let w' p:= pin V (loose T p); let P p:= Real.exp (-((k+1:ℕ)*v)*size (p a-w' p j))*K*(F' (u p)*G' (w' p))
    refine ⟨P,fun p=> hc _ _ _ _ _ ?_ ?_,fun x=>?_⟩
    · rw [only_pin ha.1 (loose T p)]; have hh: Pail (u p b) w _ _:=hF (u p); rw [show u p b=p a from congr_fun (pin_loose T p) a] at hh; exact hh
    · rw [only_pin hg.1]; exact hG (w' p)
    have hh := par_knots ht h a b j (by rfl) hv hw hk (fun p=>Ink.nonneg (hF p)) (fun p=> Ink.nonneg (hG p)) hK ha.pos hg.pos hP hM x
    convert hh using 1
    funext y; dsimp only [P]; rw [show y.val a=x from y.property]

variable {M:Row X X} {F:Places I→Rooted (Poise U D R) X (r+1)} {G:Places I→Rooted (Poise V D R) X (s+1)}
def strip_need (k r s:ℕ)(v:ℝ):=(k+1:ℕ)*v+v*((r:ℝ)+s+1)
lemma pair_mark (ht:T=U∪V)(h:Disjoint U V)(hs:V.Nonempty)(hu:U.Nonempty)(hv:0<v)(hw:strip_need k r s v ≤ w)(hx:U.card≤k)(hk:V.card ≤ k)(hK:0≤K)(hp:M.strip w K)(hF:Owns w U F A)(hg:Owns w V G B) :
    Owns v T (fun p:Places I=> wounds none T M (F p) (G p)) ((‖syl r s‖*K)*(A*(B*shells v))) := by
    let z:= ‖syl r s‖*K; have he:0≤z:=mul_nonneg (norm_nonneg _) hK
    have ha:=hF.pos; have hb:=hg.pos; have hl:=shells_pos hv
    refine ⟨fun a b hv=> congr_arg₂ _ (hF.1 a b (fun i hi=> hv i ((ht.symm ▸ (subset_union_left (s₂:=V))) hi))) (hg.1 a b (fun i hi=> hv i ((ht.symm ▸ (subset_union_right (s₁:=U))) hi))),mul_nonneg he (by positivity),fun a=>?_⟩
    let θ:ℝ:= ((k+1:ℕ):ℝ)*v; have hθ:0≤θ:=mul_nonneg (by positivity) hv.le
    have hw' : v≤ w:= (by unfold strip_need at hw; push_cast at hw; nlinarith [show 0≤v*(r+s:ℝ) by positivity,show 0≤(k:ℝ)*v by positivity])
    have hU:a.val∈U∨a.val∈V:=mem_union.mp (show a.val∈U∪V from ht ▸ a.property)
    rcases hU with hU|hU
    · refine we_go (H:=fun p:Places I=> wounds none T M (F p) (G p)) ht h hs hv hw' hk he hF hg ?_ a hU
      intro x i j u v' H H'; apply Ink.raise (pulses_pair T H H' (o:=i) (Or.inl rfl) hv.le hθ hw hp hK) (le_of_eq ?_); unfold θ z; ring
    change ∃ U:Fleet T→ℝ,_∧ ∀ x, SumBudget _ (z*(A*(B*shells v)))
    rw [show z*(A*(B*shells v))=z*(B*(A*shells v)) by ring]; refine we_go (H:=fun p:Places I=> wounds none T M (F p) (G p)) (ht.trans (union_comm ..)) h.symm hu hv hw' hx he hg hF ?_ a hU
    intro x i j u v' H H'; apply Ink.raise (pulses_pair T H' H (o:=i) (Or.inr rfl) hv.le hθ hw hp hK) (le_of_eq ?_); rw [vibrate_sym i j]; unfold θ z; ring
end YM.RG08.Wax
