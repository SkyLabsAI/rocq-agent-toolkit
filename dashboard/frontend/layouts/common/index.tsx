import { Logo } from "@/icons/logo/logo";

const Layout = ({ title,children }: { title: string;children: React.ReactNode }) => {

  return (
    <div className="min-h-screen bg-linear-to-br from-slate-900 via-slate-800 to-slate-900">
      <div className="max-w-7xl mx-auto px-4 sm:px-6 lg:px-8 py-8">
        {/* Header */}
        <div className="flex items-center justify-center mb-8">
          <div className="flex items-center gap-4 bg-white/5 backdrop-blur-sm border border-white/10 rounded-2xl px-8 py-4">
            <Logo  />
            <h1 className="text-4xl font-bold bg-linear-to-r from-blue-400 to-purple-400 bg-clip-text text-transparent">
              {title}
            </h1>
          </div>
        </div>
        
        {children}
      </div>
    </div>
  );
}


export default Layout;