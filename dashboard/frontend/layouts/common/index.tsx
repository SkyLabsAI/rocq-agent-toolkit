import ThemeSwitcher from "@/components/ThemeSwitcher";
import { LogoIcon } from "@/icons/logo/logo";

const Layout = ({ title,children }: { title: string;children: React.ReactNode }) => {

  return (
    <div className="min-h-screen bg-elevation-surface-sunken text-text flex flex-col">
        {/* Header */}
        <div className="justify-center border-b border-elevation-surface-overlay bg-elevation-surface">
          <div className="flex items-center gap-4 backdrop-blur-sm  px-10 py-4">
            <div className="flex items-center">

            <LogoIcon  />
            <h1 className="ml-2.5 text-text font-['Noto_Sans'] text-base font-normal leading-[normal]">Skylabs AI</h1>
            </div>
            <div className="h-7 w-px mx-4.5 bg-text-accent-gray "></div>
            <h1 className="text-text-subtlest font-['Noto_Sans'] text-base font-normal leading-[normal]">
              {title}
            </h1>
            <ThemeSwitcher className="mr-2" />
          </div>              
        </div>
        
      <div className=" px-10  mt-24">
        {children}
      </div>
    </div>
  );
}


export default Layout;