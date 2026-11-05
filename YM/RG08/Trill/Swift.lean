import YM.RG08.Trill.Tact
import YM.RG08.Trill.Mars
import YM.RG08.Yurt.Route
import YM.RG08.Halo.Kumi
/-! # One format combines receipts for certified primary projections on deterministic legs only. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Trill
open Forms Function Finset Jetty Lattice Isles Pert.Bulk Skiff Trickle
open Room Gallery Camera Glyph Quarry Weald Hatch Carrel Laurent Filter Stationary Spar Flint
open Planned.PrimaryIntegral295 Place Film Labels Source Source.Drops WardBin Parts Lagoon Yurt Halo
open RG Precision Next.Free
open scoped Classical ContDiff BigOperators Topology ENNReal ComplexConjugate Matrix.Norms.Frobenius
variable {G:Gauge}{d n p l e D k j t h:ℕ}{σ τ B Q:ℝ}
local notation "E₀"=>Ed G Cover
local notation "Y"=>Snap G d
local notation "N"=>Nd G Cover
local notation "A₀"=>Loc G 1
variable (X:Labels.Frame G d)

lemma foreLyrics {L:Patch}(K:KernelChoices)(b:Bed)(P:GrainS (Ed G Cover))(F : Ready D G n (P e n)){σ C:ℝ}(h:RowCost σ L.L (Cell.plotted L K G b) C)(hp:0<σ)(hc:0<C)(p:ℕ): Lyrics (forecast L K b P p e n) ∧ (∀ f:Pearl,Forms.Sym (fun i=>forecast L K b P p e n i f)):=by
 obtain ⟨s,hs,c,hw,hf⟩:= F.well; let V:=P e n;let J:=Cell.plotted L K G b
 let I:=Site L.L
 let g(o:I):= Yurt.ferry J V (Carrier.unitStep L.L) (Lagoon.ahead L.L o) (lift o); let a:ℝ:= (L.L.val:ℝ)^p/(Fintype.card I)
 have hg(o:I): Lyrics (g o):= (ferry_lives _ h hc hp hs hf hw F.coherent o).1
 have he:forecast L K b P p e n=a • ∑ i:I,g i:=by unfold Yurt.forecast;rw [Pi.smul_apply,Pi.smul_apply,Finset.sum_apply,Finset.sum_apply];unfold a g I V J; simp_rw [Yurt.fabled L K b P]
 rw [he];refine ⟨(Lyrics.sum univ (f:=g) (fun _ _=>hg _)).smul _,?_⟩;intro f u;funext i
 change a*(∑ j:I,g j) (i ∘ u) f=a*(∑ j:I,g j) i f; rw [Finset.sum_apply,Finset.sum_apply,Finset.sum_apply,Finset.sum_apply];congr 1;apply sum_congr rfl;intro o _
 let F':=Lagoon.aisle (Carrier.unitStep L.L) (Lagoon.ahead L.L o) f
 change sonic V F' (fun j=>tender J (lift o) 0 (i (u j)))=sonic V F' (fun j=>tender J (lift o) 0 (i j))
 exact sonic_swap F' (F.turned _) (fun j=> tender J (Lattice.lift o) 0 (i j)) u

/-- Closed single-rank receipts. Comparator Calendar or horizon V_r.
 χ_toll measured by actual same-order projection coordinates (full Π rank crossing).
 Quant outputs (receipt fuel form) include unchanged forecast π0 small PLUS exact leading at leading weight w
 for triangular same-slot. Powers structure sharp; none here post claim uniform additional work.
- input slot 0, preimage and address transformation tested before deflation.
- F called (normalized own g) compatible. Assume rowcosts prewidth K,N,post prices Q (doesn't shrink σ δ).
-/
theorem podium (Ho:Hol G)(D _d' l e n j t:ℕ)(σ τ η δ V:ℝ)(hs:0<σ)(ht:0<τ)(hη:0<η)(hV:0≤V)(hr:n≤l+e)(hj:4≤j)(hk:4≤t)(hd:d+1≤D)(hJ:d≤j)(hδ:0≤δ)(hδ':δ≤1)(hw:(↑((e+1)*(l+e)):ℝ)*δ≤σ/2)(he:2*η≤τ)(K:KernelChoices): -- d' unused
 ∃ C:ℝ,0≤C∧ ∀ (L:Patch)(F:Flight j t)(b:Bed)(P:GrainS (Ed G Cover))(G':Kernel G.ColorIndex A₀)(ha:L.L=F.L){Q T T' B χ:ℝ}(w:ℕ),
 let U:=(ha.symm ▸ Carrier.linesOf F K.penalty); let A:=Cell.plotted L K G b
 ; Odd L.L.val→RowCost τ L.L G' Q→RowCost τ L.L A Q→0<Q→ Tutor L.L τ V U G d→Crest L.L U G' A→(2*η)/(L.L.val:ℝ)≤δ→η*Carrier.unitStep L.L≤σ/2→Calls l P→ Permit D l P→0≤T→0≤T'→0≤B→0≤χ→(∀ k≤l+e,Sings (stance _) D hs (P e k) T)→Sings (stance _) D hs (P e n) T'→ (∀ i<e,∀ k≤l+i,Sings (stance _) D hs (P i k) B)→(∀ c:Accent X,(X.grades c.ear).2=n→|project X P e c|≤χ)→w≤d→(w=0 ∨ ( B=0 ∧ ∀ c:Accent X,(X.grades c.ear).2=n→ (X.grades c.ear).1+Trill.weight c.test.play<w→ project X P e c=0))→
 let J:=forecast L K b P d e n;let O:=P e n;let a:ℝ:= L.L.val
 let Ω:=C*((Q+V)^n*B*a^d+(χ+B)*a^(d-w))
 Sings (stance _) D hη J (C*T'* Carrier.unitStep L.L+C*((Q+V)^n*B*a^d+(χ+B)*a^d)) ∧ (∀ c:Accent X,(X.grades c.ear).2=n→ |pix X c.ear c.test.play J|≤ Ω ∧ ((X.grades c.ear).1+Trill.weight c.test.play≤w→B=0→pix X c.ear c.test.play J=a^(d-((X.grades c.ear).1+Trill.weight c.test.play))*pix X c.ear c.test.play O)):=by
 obtain ⟨α,hα,S⟩:= chime X D n l e σ hs Ho
 obtain ⟨a,ha,A⟩:=Yurt.soar0 G l d D e n τ V σ η δ hη hs hV ht hd hr hδ hδ' hw he
 obtain ⟨b,hb,B⟩:= Halo.baton G l e n d D j t σ τ V hs ht hV hr hj hk hJ K
 choose c hc H using fun (o:Accent X)=>single_chord X o
 let v:=∑ i,c i; have hv:0≤v:=sum_nonneg fun i _=>hc i
 have hY(i):c i≤v:=single_le_sum (s:=univ) (f:=c) (fun i _=>hc i) (mem_univ i)
 let C':=(v*b+a)*(1+α); have hC:0≤C':=by unfold C';positivity
 refine ⟨C',hC,?_⟩
 intro L F b' P G' hA Q T T0 B' χ w U M hL hG HM hQ hU h'g h'D h'D' hW hP hT ht0 hB hχ H' HS HG hh hX hCw J O r Ω
 have hu:Tutor L.L τ V U G 0:=fun o ho=>hU o (ho.trans (Nat.zero_le _))
 have hf :Halo.Tuned G n d D w σ hs O (α*(B'+χ)):= S B' T χ hW hP hB hT hχ HG H' hh w (by omega) hCw
 have hr0:(0:ℝ)≤r:=Nat.cast_nonneg _
 have hr'(k:ℕ): (0:ℝ)≤r^k:=by positivity
 let n':=(Q+V)^n; have hN:0 ≤ n':=by unfold n'; positivity
 have hC':a*(1+α)≤C':=mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) (by positivity)
 have hY'(i):c i*b*(1+α)≤C':=mul_le_mul_of_nonneg_right (le_trans (mul_le_mul_of_nonneg_right (hY i) hb) (le_add_of_nonneg_right ha)) (by positivity)
 have hCU :a≤C':=le_trans (le_mul_of_one_le_right ha (by linarith only [hα])) hC'
 have hc'':a*α≤C':=le_trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) ha) hC'
 have hRV:0≤Carrier.unitStep L.L:=(Carrier.unitStep_pos L.L).le
 let W:=a*T0* Carrier.unitStep L.L+a*r^d*((Q+V)^n*B'+α*(B'+χ));have hW':0 ≤ W:=by unfold W; positivity
 have h₁:Sings (stance _) D hη J W:= A L K b' U G' P hL hU h'g h'D h'D' hG hQ.le hW hP hT ht0 (by positivity) hB hf.sturdy H' HS HG
 constructor
 · refine h₁.mono le_rfl le_rfl (fun _=>le_rfl) ?_
   have h1:=mul_le_mul_of_nonneg_right hCU (show 0≤T0*Carrier.unitStep L.L by positivity)
   have h2:=mul_le_mul_of_nonneg_right hCU (show 0≤n'*B'*r^d by positivity)
   have h3:=mul_le_mul_of_nonneg_right hc'' (show 0≤(B'+χ)*r^d by positivity)
   change a*T0*Carrier.unitStep L.L+a*r^d*(n'*B'+α*(B'+χ)) ≤ C'*T0*Carrier.unitStep L.L+C'*(n'*B'*r^d+(χ+B')*r^d)
   nlinarith only [h1,h2,h3]
 intro o ho;let q:=Trill.weight o.test.play;let m:=(X.grades o.ear).1
 have hx:=H o; dsimp only at hx; rw [ho] at hx
 obtain ⟨hF,hI⟩:=foreLyrics K b' P (permit_ready hP (e:=e) (n:=n)) HM ht hQ d
 have Hp:Ready D G n J:=⟨hF,hI,η,hη,W,hW',h₁⟩ --
 have Hp':Ready D G n O:=permit_ready hP
 let Z:= b*(n'*B'*r^d+α*(B'+χ)*r^(d-w));have hZ:0≤Z:=by unfold Z;positivity
 have hE(ψ:Fin n→Masked G)(b0:Fin n→ℕ)(a:Fin n→ℝ)(h2:(∑ i,b0 i)=m)(hu':∀ i,1≤b0 i)(h4:∀ i,Chit G (b0 i) (ψ i) (a i))(s:Jetty.Cargo q):=
   B P F L b'  (w:=w) hA hW hP hf hX hT hQ.le hB HG H' hG HM hu h'g q s (by rw [h2,Nat.add_comm];exact o.joint) hu' h4
 constructor
 · have ht':=hx J O D 0 Z Hp Hp' hZ (fun f g D h3 h4 h5 s=>by rw [zero_mul,sub_zero]; exact (hE _ _ _ h3 h4 h5 s).1)
   rw [zero_mul,sub_zero] at ht'
   apply ht'.trans
   have hC1:c o*b≤C':= (le_mul_of_one_le_right (by positivity [hc o]) (show 1≤1+α by linarith)).trans (hY' o)
   have hC2:c o*b*α≤C':=(mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (a:=α) zero_le_one) (show 0 ≤ c o*b by have ht:=hc o; positivity)).trans (hY' o)
   change c o*(b*(n'*B'*r^d+α*(B'+χ)*r^(d-w)))≤ C'*(n'*B'*r^d+(χ+B')*r^(d-w))
   nlinarith only [mul_le_mul_of_nonneg_right hC1 (show 0≤n'*B'*r^d by positivity),mul_le_mul_of_nonneg_right hC2 (show 0≤ (χ+B')*r^(d-w) by positivity)]
 intro hw hN;subst B'
 apply sub_eq_zero.mp;apply abs_eq_zero.mp;apply le_antisymm _ (abs_nonneg _)
 have he:= hx J O D (r^(d-(m+q))) 0 Hp Hp' le_rfl (fun f g A h3 h4 h5 s=>?_ )
 · rw [mul_zero] at he;exact he
 have he: q+∑ i,g i≤ w:=by rw [h3,Nat.add_comm];exact hw
 rw [show sonic J (pal s) (Yurt.inlet ∘ f)=r^(d-(q+∑ i,g i))* sonic O (pal s) (Yurt.inlet ∘ f) from (hE _ _ _ h3 h4 h5 s).2 he rfl,h3,Nat.add_comm q,sub_self,abs_zero,zero_mul]
end YM.RG08.Trill
