import YM.TraceExtension.Loft.Earth
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Loft
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Audience Metric Lamp Det
open scoped BigOperators Topology ContDiff ComplexConjugate Classical
variable {W:Type}{G:Gauge}{g:W→ Side}{q:Clip}{k m n:ℕ}{σ A B C D μ a r:ℝ}
abbrev Coast (k:ℕ)(G:Gauge)(W:Type):= W→ TubeF G k
def Sand (U: Coast k G W): Prop:= ∀ (E:Type)(x:E→W)(X:Burst E (Fslot G))(T μ:E→ ℝ)(r:ℝ), ColdR X T μ r → ∀ j, X.mark=(fun _=>j)→ Sib (U ∘ x) j∧Tall X (T^2) (fun w=> summitM (U (x w)) (μ w))
lemma vista {R:W→PathData G}{L:Skuta W G}{V:Jar G}(h:Cred g q R L V σ a A C D):
    Sand (Border (L.useJar V)) ∧ Sand (fun _:W=> quarry G):=by
    have hp:=h.σp; have hx:=add_nonneg h.cb h.ac
    obtain ⟨P,E,hP,hE,H,hK⟩:= hotbase (fun i=>(L.light i).combine V) (fun i=> (h.live i).2.1.pay h.hat) hp hx
    constructor
    · intro E x X T μ r he j hv; let S:Skuta E G:=⟨L.light ∘ x,L.terra ∘ x,L.top ∘ x,L.σ ∘ x,L.μ ∘ x⟩; have hh:S.Live σ D a C V:=fun i=> h.live _
      exact ⟨sib j (Floe.vector hh hp h.grey h.hat X r) (congr_fun hv) hp hP (fun i=> H (x i)), alp_t (F:=S.useJar V) (B:=S.terra) (p:=S.top) he h.εp (fun i=>(hh i).1)⟩
    exact fun _ _ X T μ r h j hv=>⟨sib j (Floe.ghost X r) (congr_fun hv) hp hE (fun _=>hK),cinderTall h⟩
abbrev peakT {s:Side}(i:Site s)(μ:ℝ):ℝ:= flay (sip i)+μ
def Rount (g:W→Side):= Sigma fun i=> (Site (g i) × Set.Ioc (0:ℝ) 1)
variable {V: Coast k G W}(h:Sand V)(b:Fslot G) (u v:Track)
structure Payoff (n:ℕ)(A t:ℝ)(j i: Loc G k)(a:Fslot G)(U:TubeF G k)(x p q:Track): Prop where
    tab: Allows n (fun _t:ℝ=> legA U x j i) 0 (A*(t^ (2:ℕ))⁻¹)
    spot: Allows n (fun r:ℝ=> legB U a (r • t • p,x) j i) 0 (A*(t^(3:ℕ))⁻¹)
    clap: Allows n (fun r:ℝ=> legB U a (r • t • q,x) j i) 0 (A*(t^(3:ℕ))⁻¹)
    arch: Allows n (fun r:ℝ=>legC U a a (r • t • p,r • t • q,x) j i) 0 (A*(t^(4:ℕ))⁻¹)
include h
lemma peaks (j i: Loc G k)(g:W→Side):∃ C:ℝ,0≤ C ∧ ∀ (w) (x:Site (g w))(m:ℝ), m∈Set.Ioc (0:ℝ) 1 → Payoff n C (peakT x m) j i b (summitM (V w) m).back (sip x) u v:=by
   let f(p:Rount g):W:=Sigma.fst p; let y(p:Rount g): Site (g (f p)):= p.2.1; let μ(p:Rount g):ℝ:=p.2.2.val; let X:Burst (Rount g) (Fslot G):=⟨fun p=>sip (y p),fun _=>step 0,fun _=>b⟩; let T (p:Rount g):= peakT (y p) (μ p)
   have hh: ColdR X T μ furthest:=globe (fun w=> w.2.2.property) (fun w=>sip_n _) (fun w=>singleStep _)
   obtain ⟨hc,he⟩:=h _ f X T μ _ hh b rfl
   obtain ⟨P,hP,H⟩:=((pact_cap b hh hc he (n:=n) 0).tag j i).keep
   obtain ⟨A,hA,K⟩:=((pact_b b hh hc he u 0 (n:=n)).tag j i).keep
   obtain ⟨E,hE,S⟩:=((pact_b b hh hc he v 0 (n:=n)).tag j i).keep
   obtain ⟨D,hD,M⟩:=((pact_c b hh hc he u v (n:=n)).tag j i).keep
   have hp(w:Rount g)(t:ℝ):rankP X T 0 w t=X.lens w:=by simp[rankP,Mint]
   simp_rw[hp] at H K S
   refine ⟨P+A+E+D,by positivity,fun w x m hm=>?_⟩; let W' : Rount g:=⟨w,x,m,hm⟩
   have ht:=hh.lower W'
   have hv(n:ℕ)(r:ℝ)(h:r≤ P+A+E+D): r*(T W'^n)⁻¹ ≤ (P+A+E+D)* (T W'^n)⁻¹:=mul_le_mul_of_nonneg_right h (by positivity)
   exact ⟨(H W').mono (hv _ _ (by linarith)), (K W').mono (hv _ _ (by linarith)), (S W').mono (hv _ _ (by linarith)),(M W').mono (hv _ _ (by linarith))⟩
end YM.Trace.Loft
