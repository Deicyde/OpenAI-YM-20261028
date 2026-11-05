import YM.RG08.Anchor.Curls
import YM.RG08.Packets.Lines
import YM.RG08.Packets.Swing
import YM.Pert.Bulk.Keys

/-!
# Export rooted bounds on analytic deterministic all-legs contributions at prelength gain,
DIFFERENT input and output widths (crucial for canonical lift after this contribution).
With identification as same Forms tensor contraction.
-/
noncomputable section
namespace YM.RG08.Spar
open Forms Rudder Packets Finset Function Lattice Laurent Pert.Bulk Exterior Filter Bloch Anchor
open scoped Topology BigOperators Classical ENNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {I α β:Type}{n:ℕ}{L:Side}{ω σ τ C A:ℝ}

/- Atlas lift to dummies/colors (same pre prices). -/
def prism (I: Type)(K:Kernel α β):Kernel (α×I) (β×I):=fun x y=> if x.2.2=y.2.2 then K (x.1,x.2.1) (y.1,y.2.1) else 0
lemma prism_prices (K:Kernel α β) (I:Type){d:ℕ}(h:Atlas σ L d K A):Atlas σ L d (prism I K) A:=by
 refine ⟨h.width,h.nonneg,fun ⟨x,i,c⟩ ⟨j,e⟩=>?_,fun ⟨i,c⟩ ⟨x,j,e⟩=>?_,fun a ⟨x,i,c⟩ ⟨j,e⟩=>?_⟩ <;>
 obtain hc|hc:=eq_or_ne c e <;> unfold prism
 · simpa only [hc,if_true] using h.row (x,i) j
 · simp [hc,Pert.Bulk.bill]
 · simpa only [hc,if_true] using h.col i (x,j)
 · simp [hc,Pert.Bulk.bill]
 · simpa [foot,hc] using h.step a (x,i) j
 simp [foot,hc,Pert.Bulk.bill]

lemma prism_city (K:Kernel α β)(I:Type)(h:city L K):city L (prism I K):=by
 intro ⟨x,i,c⟩ ⟨y,j,e⟩ u;unfold prism;change (if c=e then K _ _ else 0)=_;split_ifs
 exact h (x,i) (y,j) u
 rfl

def braces (K:Kernel α β)(F:Flake n (Market α)):= raft (fun _=>K) F

lemma braces_path {K: Kernel α β}{F:Flake n (Market α)}(h: city L K)(hp:Cohort F):Cohort (braces K F):=by
 intro v y; unfold braces raft;rw [←(tides (L.val • v)).tsum_eq];apply tsum_congr; intro x
 unfold vat design;rw [show F (tides (L.val•v) x)=F x from hp ..];congr 1; apply prod_congr rfl;intro i _;exact h (x i) (y i) v
lemma braces_sym {K:Kernel α β}{F:Flake n (Market α)}(h:Forms.Sym F):Forms.Sym (braces K F):=by
 intro e;funext x
 unfold woven braces raft
 rw [← (twist e).tsum_eq (fun v=>vat _ F (x ∘ e) v)]
 apply tsum_congr;intro v
 have he:F (twist e v) =F v:=congrFun (h e) v
 unfold vat design;rw [he];congr 1;exact Equiv.prod_comp e (fun j=>K (v j) (x j))

variable [Fintype α][Fintype β] {F:Flake (n+1) (Market α)}{K:Kernel α β}

lemma bridge_push (h:Atlas ω L 2 K A)(hp:Folded τ (Forms.spin F) C)(hτ:0≤τ):
 Forms.spin (braces K F) = Packets.push (Forms.spin F) K (fun _ _=>K):=by
 funext y x
 have he:= (mixed_lines (t:=fun _=>A) (σ:=0) (K:=Forms.spin F) (L:=L) h (fun _=>h) hp le_rfl h.width (by simpa only [mul_zero] using h.width) (by positivity)).2 x y
 rw [push_full (K:=Forms.spin F) (U:=fun _ _=>K) (T:=K) y x he, Forms.spin,braces,raft, ←(Fin.consEquiv (fun _:Fin (n+1)=>Market α)).tsum_eq (fun w=>vat _ _ _ w)]
 apply tsum_congr;rintro ⟨a,b⟩
 change vat _ _ _ (Fin.cons a b) = _
 unfold vat term design Forms.spin
 rw [Fin.prod_univ_succ]; simp [mul_assoc,mul_comm];ring

lemma vessel (h:Atlas ω L 2 K A)(hp:Held (carpet α) ((n:ℝ)*τ) C F)(hτ:0≤τ)(hF:Forms.Sym F)(hs:0≤σ)(hσ:2*σ≤ω)(hn:(n:ℝ)*(2*σ)≤ω)(hw:2*σ≤L.val*τ)(hr:2≤n)(hC:0≤C):
 Held (carpet β) σ ((Fintype.card β*A)^n*(Fintype.card α*A)*C/(L.val:ℝ)^2) (braces K F):=by
 have hh:=hp.fold hτ
 apply Held_of_folded (braces_sym hF) hs
 rw [bridge_push h hh hτ]
 have ht:=mixed_lines (t:=fun _:Fin n=>A) (σ:=2*σ) h (fun _=>h) hh (by positivity) hσ hn hw
 intro v
 apply (ht.1 v).trans
 apply ENNReal.ofReal_le_ofReal
 unfold packetCoin;rw [prod_const,card_univ,Fintype.card_fin,mul_comm ((Fintype.card α:ℝ)*_)]
 exact deep_bound _ _ _ _ hC h.nonneg (by positivity) (by positivity) hr

lemma charged (h:Atlas ω L 2 K A){F:Flake 2 (Market α)}(hp: Held (carpet α) τ C F)(hτ:0<τ)(hF:Forms.Sym F)(hN: neutral (Forms.spin F))(hs:0≤σ)(hσ:2*σ≤ω)(hw:2*(2*σ)≤L.val*τ):
 Held (carpet β) σ (neutralCoin L α β τ A A*C) (braces K F):=by
 have hh:=Held.fold (n:=1) (I:=α) (σ:=τ) (F:=F) (by simpa using hp) hτ.le
 apply Held_of_folded (braces_sym hF) hs
 rw [bridge_push h hh hτ.le]
 exact push_null h h hh hτ (by positivity) hσ hw hN
end YM.RG08.Spar
