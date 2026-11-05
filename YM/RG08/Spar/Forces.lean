import YM.RG08.Spar.Bows

/-! Cost of `picture` and unchanged re-choose bandwidth for repeated curvature contribution.
-/
noncomputable section
namespace YM.RG08.Spar
open Forms Rudder Packets Finset Function Lattice Laurent Pert.Bulk Exterior Filter Bloch Anchor Symmetry
open AnalyticNext.QuarticMatch.BoxChain hiding sway
open scoped Topology BigOperators Classical ENNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {I:Type}{n:ℕ}{σ C Q:ℝ}{F:Raw I n}

lemma charge_last (s:List (Fin n))(hp:NextTo F σ C):NextTo (patchL s F) σ (debit σ^s.length*C):=by
 intro y;rw [patch_eval]; have he:=hp y
 induction s generalizing F C with
 | nil=> simpa only [List.length_nil,pow_zero,one_mul,solve_empty] using he
 | cons j l ih=>
    -- redundant hp and y
    change Pricing (YM.AnalyticNext.QuarticMatch.BoxChain.solve l (lower j (hum F y))) _ _
    have hp':NextTo (boundary j F) σ (debit σ*C):=fun z=>(hp z).smaller j
    convert ih hp' (he.smaller j) using 1 <;> first | rfl | (rw [List.length_cons,pow_succ];ring)

lemma photograph (hp:NextTo F σ C):NextTo (picture I n F) σ (debit σ^n*C):=by simpa only [picture,List.length_finRange] using charge_last (List.finRange _) hp
variable [Fintype I]

def flashes (I:Type)[Fintype I](n:ℕ)(σ:ℝ):ℝ:=debit' (Tone I) n σ * debit σ ^ n
lemma flame_pos (h:0<σ)(hn:0<n):0≤flashes I n σ:=mul_nonneg (debit'_nn h hn) (pow_nonneg (debit_pos _) _)
lemma encode (hn:0<n)(h:0<σ)(hc:0≤C)(hF:Cohort F)(hk:Held (carpet (Tone I)) σ C F):
 Held (carpet (Tone I)) (σ/2) (flashes I n σ*C) (picture I n F):=by
 unfold flashes;rw [mul_assoc];exact (photograph (NextTo.unit h hc hF hk hn)).held hn (mul_nonneg (pow_nonneg (debit_pos _) _) hc) h

variable {K:Kernel (TypeFace 2) (TypeFace 2)}{L:Side}{ω A:ℝ}
/- neutral check adapter from curvature zero Fourier value -/
lemma standby {G:Gauge}{F:Raw G.ColorIndex 2}(h:Rudder.Loop.Core F 0)(hp:Cohort F):Pert.Bulk.neutral (Forms.spin (compress 2 F)):=by
 intro x β
 rcases x with ⟨x,a,i⟩;rcases β with ⟨b,j⟩
 let y:Tape 2 G.ColorIndex:=Fin.cons i (fun _=>j)
 let T:=hum F y
 have he:=h a.val b.val a.property b.property y
 have H(v:Cover):Forms.spin (compress 2 F) (x,a,i) (fun _:Fin 1=>(v,b,j))=Loop.col T a.val b.val (v-x):= by
    refine Eq.trans ?_ (Loop.prices (show Cohere T from fun t w=>hp t (lyre w y)) (x,a.val) (v,b.val));apply congr_arg F;ext i':1;cases i' using Fin.cases with
    | zero=>rfl
    | succ i' => rw [Subsingleton.elim i' (0:Fin 1)];rfl
 simp_rw [H];rw [show ∑'v:Cover,Loop.col T a.val b.val (v-x)=∑'v:Cover,Loop.col T a.val b.val v from (Equiv.subRight x).tsum_eq _];change Loop.spectrum F a.val _ _ = _;rw [he];simp [Loop.AxisK]

/- Result is the re-aggregation between the two bases. This is the kernel whose equality
to the unchanged terms from A_tr needs to be checked on the consumers; estimate holds
regardless. -/
def pushField (K:Kernel (TypeFace 2) (TypeFace 2))(F:Raw I n):Raw I n:=
 Anchor.extend 2 (braces (prism I K) (compress 2 F))
def voucher (K:Kernel (TypeFace 2) (TypeFace 2))(F: Raw I n) : Raw I n:=picture I n (pushField K F)

lemma lined (h:Atlas ω L 2 K A)(hK:city L K){F:Raw I (n+1)}(hf:Forms.Sym F)(hm:Cohort F)
   (hM:Held (carpet (Tone I)) σ C F)(hn:2≤n)(hC:0≤C)(hs:0≤σ)(v:ℝ)(hv:0<v)(h₀:4*v≤ω)(he:n*(4*v)≤ω)(ht: 4*v≤L.val*(σ/n)) :
 let T:ℝ:= Fintype.card (Kind I 2)
 let M:= (flashes I (n+1) (2*v))* (T*A)^(n+1)
 Held (carpet (Tone I)) v (M*C/L.val^2) (voucher K F):=by
 intro T M
 have hh:0<(n:ℝ):=by exact_mod_cast (show 0<n by omega)
 have hw:=vessel (L:=L) (ω:=ω) (prism_prices K I h) (τ:=σ/n) (σ:=2*v) (F:=compress 2 F) (show Held (carpet _) (↑n*(σ/n)) C _ by
    rw [show (n:ℝ)*(σ/n)=σ by field];exact compress_cost _ hM) (by positivity) (compress_sym _ hf) (by positivity) (by linarith) (by nlinarith) (by nlinarith) hn hC
 unfold voucher
 convert encode (I:=I) (σ:=2*v) (n:=n+1) (Nat.succ_pos _) (by positivity) (by have he:= h.nonneg; have hp:=L.pos; exact show 0≤ (Fintype.card (TypeFace 2 × I)*A)^n*(Fintype.card (TypeFace 2 × I)*A)*C/(↑L:ℝ)^2 from by positivity) (expand_path (braces_path (prism_city _ _ hK) (compress_path _ hm))) (expand_cost hw) using 1
 · ring
 · unfold M T;rw [pow_succ];ring
 rfl

lemma leads (h:Atlas ω L 2 K A)(hK:city L K){G:Gauge}{F:Raw G.ColorIndex 2}(hf:Forms.Sym F)(hm:Cohort F)(hT:Loop.Core F 0)
   (hM:Held (carpet (Tone G.ColorIndex)) σ C F)(hC:0≤C)(hs:0<σ)(v:ℝ)(hv:0<v)(h₀:4*v≤ω)(ht: 8*v≤L.val*σ) :
 let T:ℝ:= Fintype.card (Kind G.ColorIndex 2)
 let M:= (flashes G.ColorIndex 2 (2*v))* (T*A*(T*(2/σ)*A))
 Held (carpet (Tone G.ColorIndex)) v (M*C/L.val) (voucher K F):=by
 intro T M
 have hw:=charged (L:=L) (ω:=ω) (prism_prices K G.ColorIndex h) (compress_cost 2 hM) hs (compress_sym _ hf) (standby hT hm) (σ:=2*v) (by positivity) (by linarith) (by linarith)
 unfold voucher
 convert encode (I:=G.ColorIndex) (σ:=2*v) (n:=2) (by omega) (by positivity) (show 0 ≤ neutralCoin L (Kind G.ColorIndex 2) (Kind G.ColorIndex 2) σ A A*C by unfold neutralCoin;have he:=h.nonneg;positivity) (expand_path (braces_path (prism_city _ _ hK) (compress_path _ hm))) (expand_cost hw) using 1
 · ring
 · unfold M T neutralCoin;ring
 rfl
end YM.RG08.Spar
