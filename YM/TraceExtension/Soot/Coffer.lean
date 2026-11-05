import YM.TraceExtension.Soot.Skein
import YM.TraceExtension.Soot.Thrifty
/-!
 # Price of both Boots. Works at moving clocks with distributional hats.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Extraction Exponential Overlay
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
open GridApprox.Joint GridApprox
variable {V:Type}[Fintype V][DecidableEq V]{B:Census V} {G:Gauge}(C:Family G)(N k m p d:ℕ)(H:C.Makes)
variable {W:Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}{ζ:ℕ→ℕ→ℝ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (w:ℝ){j:ℕ}
set_option quotPrecheck false
open Relay
local notation "T"=> C.path
local notation "ℓ"=> C.ref d
local notation "F"=> C.labels.level d
local notation "Y!"=> C.localSection d
local notation "a!"=> C.S.a
local notation "s!"=> C.factory d N p
local notation "R"=> C.path.rep N p
variable (L:Coefficient (C.labels.level d) (C.side k p))(X:Extra.Histories.Music (C.labels.level d) C.path N p)
local notation "ζ!"=> ζ d
variable {a:ℝ} {G':Config G (C.side k p)→ℂ}{E:MergeProof.Response G (C.side k p)}{S e v':ℝ}
variable (h:Scrim C W u ψ φ δ ζ r D){b:C.label d}{Z:∀ i:ℕ,Coefficient (C.labels.level d) (C.side i p)}{g:ℕ→ℝ} {Q:ℝ}
    (J:ℕ) (K:Stock.Tabs C.path.levels)
local notation "U!"=> C.O N p ((s!).terminal b) 0
include H h K
-- reduces tested primal seam expense.Melts numerator.
lemma riches (hN:k<N) (hK:C.ref d ≤ k)(B b' q:ℝ) (ht: Buff (N:=N) G' E S L e)(hc:q>0)(he:(F).coeffSize L.x + S≤ q)(hx:4*(1+(C.path.levels.params k).columns)*q ≤ B)(hm: Melts 1 (C.path.levels.budget k) a (C.path.levels.clock.forcedAllowance k) v') (hD: e*ζ d k ≤ v'*B) (hB:SharpRead C N k p d (W:=W) b'):
    ∃ b:C.label d,
       b'*(F).coeffSize (L.x-((s!).entries k ((s!).terminal.symm b)).x) ≤ 4*(1+(C.path.levels.params k).columns)*q ∧
       ∀ (J m l:ℕ)(hF: Stock.Tabs.opens C.path.levels 1 J m), C.ref d ≤ m →∀ hk:m<k, GridApprox.room C.path.levels J k l → Interior (GridApprox.window 0 l) G'→ let w:= a*((ζ d m/2)/(‖alto T m d‖*(B/gainChart T k m))); (center C.S p (hF.1.trans (hk.trans hN|>.le)) 0).rootTest (C.beta N p) (backTo T N p hN.le G'- C.O N p b 0) ≤ stakes C J m/w:=by
    obtain ⟨M,hM,hL,hP,hA⟩:= (h.costs.aim d N p (hK.trans hN.le)).lyrics
    obtain ⟨v,hU,hv⟩:= prevails C N k p d H L M S h q B b' hB hN.le hK hL hP ht.shell ht.sound he hx hc
    let b:= (s!).terminal v; have hl :(s!).terminal.symm b=v:= LinearEquiv.symm_apply_apply ..
    refine ⟨b,?_,fun J m l hF hp hk hs hh=> ?_⟩
    · rw [hl,hM,(show ((M.draft T).inits k v).x= _ from (hL.earned k hK hN.le).currents v)]; exact hU
    let u:=((ζ d m/2)/(‖alto T m d‖*(B/gainChart T k m))); intro w; have hW:w=a*u:=rfl
    have he:= h.grows d m hp; have hg:0 < a:=hm.1; have hz : a ≤ 1:=hm.2.1; have hG: 0<v'∨v'=0:=by have h:=hm.2.2.1; grind
    have hΔ:= Real.exp_pos (show ℝ from (C.S.scale k-C.S.scale m))
    have hB' :0 < B:= by refine lt_of_lt_of_le (mul_pos (show 0<(4*(1+(C.path.levels.params k).columns):ℝ) by positivity[(C.path.levels.params k).columns_ge]) hc) hx
    let t:= ‖alto T m d‖*(B/gainChart T k m); have h0: 0<t:=mul_pos (by rw[alto_norm]; positivity[C.S.a_pos m]) (div_pos hB' (Real.exp_pos _)); have hu:0<u:= div_pos (half_pos he) h0
    have h':u*t=ζ d m/2:=div_mul_cancel₀ _ h0.ne'; have hw:0<w:=hW ▸ mul_pos hg hu
    have h₀:w/u=a:= (div_eq_iff hu.ne').2 hW
    obtain ⟨V,t',hθ⟩:=hv m w hp hk.le hw (by
        rw [mul_assoc]; apply le_trans (c:=ζ d m/2) _ h'.le; exact mul_le_mul_of_nonneg_right (show w ≤ u by rw [hW]; exact mul_le_of_le_one_left hu.le hz) h0.le)
    obtain ⟨v₁,t₁,h₁'⟩:=hv m u hp hk.le hu (by rw [mul_assoc]; exact h'.le)
    apply underS C N k m p d H w L M h J K hN hp hk hw hθ hL hP hA (a:=a) (v':=v') _ ht _ hm hF l hs hh
    · rw [show w/a=u from (div_eq_iff hg.ne').mpr (by rw[hW,mul_comm])]; exact h₁'.pay
    have hl:=diet T d m φ (fun i=>ζ d i/2) u hu (fun i he=>(h.costs.stay.water i (Nat.zero_le _)).1) (fun i hi=> by have hu:= div_le_div_of_nonneg_right (h.jump d i (hp.trans hi)) (by norm_num :0 ≤ (2:ℝ)); refine le_trans (le_of_eq ?_) hu; change φ i * ((C.S.block i).val:ℝ)^(d+1)*(ζ d i/2)=_;ring) k B hB'.le (by rw [mul_assoc];exact h'.le)
    let r₀:= march (fun _:Unit=> u) φ m k (); let r':= march (fun _:Unit=> w) φ m k (); have hx : r'≤r₀:=by
        suffices h':∀ i:ℕ, march (fun _:Unit=>w) φ m i () ≤ march (fun _:Unit=>u) φ m i () from h' k
        have hw : w ≤ u:=by rw[hW]; exact mul_le_of_le_one_left hu.le hz
        intro i; induction i with
        | zero=>exact hw
        | succ i IH=> simp only [march]; split
                      next=>exact mul_le_mul_of_nonneg_left IH (h.costs.stay.water i (Nat.zero_le _) |>.1.le)
                      next=> exact hw
    specialize hl k hk.le; rw [gainChart,sub_self,mul_zero,Real.exp_zero,div_one] at hl; have h':0 ≤ e := sumBudget_credit ht.fuel.toll.choose_spec.1
    apply (mul_le_mul_of_nonneg_right hx (show _ from mul_nonneg (norm_nonneg _) h')).trans
    apply le_of_mul_le_mul_right _ hB'; change r₀*_ * B ≤ _; have hk : 0 ≤ v':=hm.2.2.1; linarith only [mul_le_mul_of_nonneg_right (show r₀*‖alto T k d‖* B ≤ ζ d k/2 from hl) h',hD,mul_nonneg hB'.le hk]
end YM.MergeProof.Accent
#print axioms YM.MergeProof.Accent.riches
